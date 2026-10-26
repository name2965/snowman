/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "SignatureAnalyzer.h"

#include <algorithm>
#include <climits>
#include <cstdint> /* uintptr_t */
#include <limits>

#include <boost/range/adaptor/map.hpp>

#include <nc/common/Foreach.h>
#include <nc/common/make_unique.h>

#include <nc/core/arch/Instruction.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/dflow/Uses.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/liveness/Livenesses.h>

#include "CallHook.h"
#include "Convention.h"
#include "Conventions.h"
#include "EntryHook.h"
#include "Hooks.h"
#include "ReturnHook.h"
#include "Signatures.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

SignatureAnalyzer::SignatureAnalyzer(Signatures &signatures, const dflow::Dataflows &dataflows, const Hooks &hooks,
                                     const liveness::Livenesses &livenesses, const CancellationToken &canceled,
                                     const LogToken &log)
    : signatures_(signatures), dataflows_(dataflows), hooks_(hooks), livenesses_(livenesses), canceled_(canceled),
      log_(log) {
}

SignatureAnalyzer::~SignatureAnalyzer() {}

void SignatureAnalyzer::analyze() {
    computeMappings();
    computeUses();
    computeArgumentsAndReturnValues();
    computeSignatures();
}

void SignatureAnalyzer::computeMappings() {
    foreach (const auto &functionAndDataflow, dataflows_) {
        auto function = functionAndDataflow.first;
        auto &dataflow = *functionAndDataflow.second;

        id2referrers_[getCalleeId(function)].functions.push_back(function);

        foreach (auto basicBlock, function->basicBlocks()) {
            foreach (auto statement, basicBlock->statements()) {
                if (auto call = statement->asCall()) {
                    auto id = getCalleeId(call, dataflow);

                    id2referrers_[id].calls.push_back(call);
                    function2calls_[function].push_back(call);

                    foreach (const auto &locationAndTerm, hooks_.getCallHook(call)->speculativeReturnValueTerms()) {
                        speculativeReturnValueTerm2calleeId_[locationAndTerm.second] = id;
                    }
                } else if (auto jump = statement->asJump()) {
                    if (dflow::isReturn(jump, dataflow)) {
                        auto id = getCalleeId(function);

                        id2referrers_[id].returns.push_back(jump);
                        function2returns_[function].push_back(jump);

                        foreach (const auto &locationAndTerm, hooks_.getReturnHook(jump)->speculativeReturnValueTerms()) {
                            speculativeReturnValueTerm2calleeId_[locationAndTerm.second] = id;
                        }
                    }
                }
            }
        }
    }
}

void SignatureAnalyzer::computeUses() {
    foreach (const auto &functionAndDataflow, dataflows_) {
        function2uses_[functionAndDataflow.first] = std::make_unique<dflow::Uses>(*functionAndDataflow.second);
    }
}

void SignatureAnalyzer::computeArgumentsAndReturnValues() {
    int niterations = 0;

    bool changed;
    do {
        changed = false;

        foreach (const CalleeId &calleeId, id2referrers_ | boost::adaptors::map_keys) {
            if (computeArguments(calleeId)) {
                changed = true;
            }
            if (computeReturnValue(calleeId)) {
                changed = true;
            }
        }

        if (++niterations > 3) {
            log_.warning(tr("Fixpoint was not reached after %1 iterations while reconstructing arguments. Giving up.").arg(niterations));
            break;
        }

        canceled_.poll();
    } while (changed);
}

namespace {

template<class Container>
bool isHomogeneous(const Container &container) {
    if (container.empty()) {
        return true;
    }

    const auto &first = *container.begin();
    foreach (const auto &value, container) {
        if (value != first) {
            return false;
        }
    }

    return true;
}

} // anonymous namespace

bool SignatureAnalyzer::computeArguments(const CalleeId &calleeId) {
    assert(calleeId);

    auto convention = hooks_.conventions().getConvention(calleeId);
    if (!convention) {
        return false;
    }

    const auto &referrers = nc::find(id2referrers_, calleeId);

    struct Placement {
        MemoryLocation inFunctions;
        boost::unordered_map<const Call *, MemoryLocation> inCalls;
    };

    boost::unordered_map<MemoryLocation, Placement> placements;

    foreach (auto function, referrers.functions) {
        foreach (const auto &memoryLocation, getUndefinedUses(function)) {
            if (auto argumentLocation = convention->getArgumentLocationCovering(memoryLocation)) {
                placements[argumentLocation].inFunctions.merge(memoryLocation);
            }
        }
    }

    foreach (auto call, referrers.calls) {
        foreach (const auto &memoryLocation, getUnusedDefines(call, convention)) {
            if (auto argumentLocation = convention->getArgumentLocationCovering(memoryLocation)) {
                placements[argumentLocation].inCalls[call].merge(memoryLocation);
            }
        }
    }

    auto getArgumentLocation = [](const Placement &placement) -> MemoryLocation {
        if (placement.inFunctions) {
            return placement.inFunctions;
        } else if (!placement.inCalls.empty() && isHomogeneous(placement.inCalls | boost::adaptors::map_values)) {
            return placement.inCalls.begin()->second;
        } else {
            return MemoryLocation();
        }
    };

    std::vector<MemoryLocation> arguments;
    boost::unordered_map<const Call *, std::vector<MemoryLocation>> extraArguments;

    foreach (auto &locationAndPlacement, placements) {
        if (auto location = getArgumentLocation(locationAndPlacement.second)) {
            if (location.addr() == locationAndPlacement.first.addr()) {
                arguments.push_back(location);
            }
        } else {
            foreach (const auto &callAndLocation, locationAndPlacement.second.inCalls) {
                if (callAndLocation.second.addr() == locationAndPlacement.first.addr()) {
                    extraArguments[callAndLocation.first].push_back(callAndLocation.second);
                }
            }
        }
    }

    arguments = convention->sortArguments(std::move(arguments));

    foreach (auto &callAndLocations, extraArguments) {
        auto &callArguments = callAndLocations.second;
        callArguments.insert(callArguments.end(), arguments.begin(), arguments.end());
        callArguments = convention->sortArguments(std::move(callArguments));
        callArguments.erase(
            std::remove_if(callArguments.begin(), callArguments.end(),
                [&](const MemoryLocation &location) {
                    return nc::contains(arguments, location);
                }),
            callArguments.end());
    }

    bool changed = false;

    auto &oldArguments = id2arguments_[calleeId];
    if (oldArguments != arguments) {
        oldArguments = std::move(arguments);
        changed = true;
    }

    foreach (auto &callAndLocations, extraArguments) {
        auto &oldExtraArguments = call2extraArguments_[callAndLocations.first];
        if (oldExtraArguments != callAndLocations.second) {
            oldExtraArguments = std::move(callAndLocations.second);
            changed = true;
        }
    }

    return changed;
}

bool SignatureAnalyzer::computeReturnValue(const CalleeId &calleeId) {
    assert(calleeId);

    auto convention = hooks_.conventions().getConvention(calleeId);
    if (!convention) {
        return false;
    }

    const auto &referrers = nc::find(id2referrers_, calleeId);

    struct Placement {
        MemoryLocation location;
        std::size_t votes;

        Placement(): votes(0) {}
    };

    boost::unordered_map<MemoryLocation, Placement> placements;

    foreach (auto call, referrers.calls) {
        foreach (const auto &memoryLocation, getUsedReturnValueLocations(call)) {
            auto &placement = placements[convention->getReturnValueLocationCovering(memoryLocation)];
            ++placement.votes;
            placement.location = MemoryLocation::merge(placement.location, memoryLocation);
        }
    }

    if (placements.empty()) {
        foreach (auto function, referrers.functions) {
            foreach (auto ret, nc::find(function2returns_, function)) {
                foreach (const auto &memoryLocation, getUnusedReturnValueLocations(ret)) {
                    auto &placement = placements[convention->getReturnValueLocationCovering(memoryLocation)];
                    ++placement.votes;
                    placement.location = MemoryLocation::merge(placement.location, memoryLocation);
                }
            }
        }
    }

    MemoryLocation returnValueLocation;

    if (!placements.empty()) {
        auto it = std::max_element(placements.begin(), placements.end(),
            [](const std::pair<MemoryLocation, Placement> &a, const std::pair<MemoryLocation, Placement> &b){
                return a.second.votes < b.second.votes;
        });

        returnValueLocation = it->second.location;
    }

    auto &oldReturnValueLocation = id2returnValue_[calleeId];
    if (oldReturnValueLocation != returnValueLocation) {
        oldReturnValueLocation = returnValueLocation;
        return true;
    } else {
        return false;
    }
}

namespace {

class StackOffsetFixer {
    boost::optional<BitSize> stackOffset_;

public:
    StackOffsetFixer(const Term *stackPointer, const dflow::Dataflow &dataflow) {
        if (stackPointer) {
            auto value = dataflow.getValue(stackPointer);
            if (value->isStackOffset()) {
                stackOffset_ = value->stackOffset() * CHAR_BIT;
            }
        }
    }

    MemoryLocation addStackOffset(const MemoryLocation &memoryLocation) {
        if (memoryLocation.domain() == MemoryDomain::STACK) {
            if (stackOffset_) {
                return memoryLocation.shifted(*stackOffset_);
            } else {
                return MemoryLocation();
            }
        } else {
            return memoryLocation;
        }
    }

    MemoryLocation removeStackOffset(const MemoryLocation &memoryLocation) {
        if (memoryLocation.domain() == MemoryDomain::STACK) {
            if (stackOffset_) {
                return memoryLocation.shifted(-*stackOffset_);
            } else {
                return MemoryLocation();
            }
        } else {
            return memoryLocation;
        }
    }
};

/**
 * Matches the expression produced for a caller-side stack cleanup. In
 * particular, x86 ADD is represented as a temporary assignment followed by
 * an assignment of that temporary to the stack pointer.
 */
boost::optional<ByteSize> getCallerCleanupSize(const Call *call, const Convention *convention) {
    assert(call != nullptr);
    assert(convention != nullptr);

    const auto &stackPointer = convention->stackPointer();
    if (convention->name() != QLatin1String("cdecl32") ||
        convention->calleeCleanup() ||
        !stackPointer ||
        stackPointer.size() != 32 ||
        convention->argumentAlignment() <= 0 ||
        convention->argumentAlignment() % CHAR_BIT != 0)
    {
        return boost::none;
    }

    auto basicBlock = call->basicBlock();
    auto callInstruction = call->instruction();
    if (!basicBlock || !callInstruction) {
        return boost::none;
    }

    /*
     * Hooks and the implicit restoration of the return-address slot can occur
     * after the Call statement. Skip those, but do not skip a real machine
     * instruction: the cleanup must immediately follow the call.
     */
    const arch::Instruction *cleanupInstruction = nullptr;
    auto statement = basicBlock->statements().get_iterator(call);
    for (++statement; statement != basicBlock->statements().end(); ++statement) {
        if ((*statement)->instruction() && (*statement)->instruction() != callInstruction) {
            cleanupInstruction = (*statement)->instruction();
            break;
        }
    }

    if (!cleanupInstruction || cleanupInstruction->addr() != callInstruction->endAddr()) {
        return boost::none;
    }

    std::vector<const Assignment *> assignments;
    const Assignment *stackPointerWrite = nullptr;

    foreach (const auto candidate, basicBlock->statements()) {
        if (candidate->instruction() != cleanupInstruction) {
            continue;
        }

        auto assignment = candidate->asAssignment();
        if (!assignment) {
            continue;
        }
        assignments.push_back(assignment);

        if (auto access = assignment->left()->asMemoryLocationAccess()) {
            if (MemoryLocation::intersect(access->memoryLocation(), stackPointer)) {
                /* A partial or second write would make the update ambiguous. */
                if (access->memoryLocation() != stackPointer || stackPointerWrite) {
                    return boost::none;
                }
                stackPointerWrite = assignment;
            }
        }
    }

    if (!stackPointerWrite) {
        return boost::none;
    }

    auto matchAddition = [&](const Term *term) -> boost::optional<ByteSize> {
        auto addition = term ? term->asBinaryOperator() : nullptr;
        if (!addition || addition->operatorKind() != BinaryOperator::ADD ||
            addition->size() != stackPointer.size())
        {
            return boost::none;
        }

        const Constant *constant = nullptr;
        const MemoryLocationAccess *access = nullptr;
        if ((access = addition->left()->asMemoryLocationAccess()) != nullptr) {
            constant = addition->right()->asConstant();
        } else if ((access = addition->right()->asMemoryLocationAccess()) != nullptr) {
            constant = addition->left()->asConstant();
        }

        if (!access || access->memoryLocation() != stackPointer || !constant ||
            constant->size() != stackPointer.size())
        {
            return boost::none;
        }

        const SignedConstantValue amount = constant->value().signedValue();
        const ByteSize alignment = convention->argumentAlignment() / CHAR_BIT;
        const BitAddr firstArgumentOffset = convention->firstArgumentOffset();
        if (amount <= 0 || amount % alignment != 0 ||
            firstArgumentOffset < 0 ||
            amount > ((std::numeric_limits<BitAddr>::max)() - firstArgumentOffset) / CHAR_BIT)
        {
            return boost::none;
        }
        return static_cast<ByteSize>(amount);
    };

    if (auto amount = matchAddition(stackPointerWrite->right())) {
        return amount;
    }

    /* Accept the canonical x86 IR form: tmp = oldSP + imm; SP = tmp. */
    auto temporary = stackPointerWrite->right()->asMemoryLocationAccess();
    if (!temporary || temporary->memoryLocation() == stackPointer) {
        return boost::none;
    }

    const Assignment *temporaryWrite = nullptr;
    bool reachedStackPointerWrite = false;
    foreach (const auto assignment, assignments) {
        if (assignment == stackPointerWrite) {
            reachedStackPointerWrite = true;
            continue;
        }
        if (auto access = assignment->left()->asMemoryLocationAccess()) {
            if (MemoryLocation::intersect(access->memoryLocation(), temporary->memoryLocation())) {
                if (reachedStackPointerWrite ||
                    access->memoryLocation() != temporary->memoryLocation() ||
                    temporaryWrite)
                {
                    return boost::none;
                }
                temporaryWrite = assignment;
            }
        }
    }

    return temporaryWrite ? matchAddition(temporaryWrite->right()) : boost::none;
}

} // anonymous namespace

std::vector<MemoryLocation> SignatureAnalyzer::getUndefinedUses(const Function *function) {
    assert(function != nullptr);

    auto &dataflow = *dataflows_.at(function);

    std::vector<MemoryLocation> result;

    /*
     * If a term reads a memory location through which an argument
     * can be passed, and nobody defines this memory location, this
     * location is likely to be actually used for passing an argument.
     */
    foreach (const auto &termAndLocation, dataflow.term2location()) {
        auto term = termAndLocation.first;
        const auto &memoryLocation = termAndLocation.second;

        if (memoryLocation && term->isRead() && dataflow.getDefinitions(term).empty() && intersect(term, memoryLocation)) {
            result.push_back(memoryLocation);
        }
    }

    /*
     * If a call has an argument whose memory location can be used
     * for passing arguments to this function, and this memory location
     * is not defined in the function, this memory location is likely
     * to be used for passing an argument.
     */
    foreach (auto call, nc::find(function2calls_, function)) {
        const auto &callArguments = nc::find(id2arguments_, getCalleeId(call, dataflow));
        if (callArguments.empty()) {
            continue;
        }

        auto callHook = hooks_.getCallHook(call);
        auto fixer = StackOffsetFixer(callHook->stackPointer(), dataflow);
        auto &reachingDefinitions = dataflow.getDefinitions(callHook->snapshotStatement());

        foreach (auto memoryLocation, callArguments) {
            memoryLocation = fixer.addStackOffset(memoryLocation);

            if (memoryLocation && reachingDefinitions.projected(memoryLocation).empty()) {
                result.push_back(memoryLocation);
            }
        }
    }

    return result;
}

std::vector<MemoryLocation> SignatureAnalyzer::getUnusedDefines(
    const Call *call, const Convention *convention)
{
    assert(call != nullptr);
    assert(convention != nullptr);

    std::vector<MemoryLocation> result;

    auto callHook = hooks_.getCallHook(call);
    auto function = call->basicBlock()->function();
    auto &dataflow = *dataflows_.at(function);
    auto &uses = *function2uses_.at(function);
    auto fixer = StackOffsetFixer(callHook->stackPointer(), dataflow);

    foreach (const auto &chunk, dataflow.getDefinitions(callHook->snapshotStatement()).chunks()) {
        foreach (const Term *term, chunk.definitions()) {
            /* Do not mistake the caller's own return-address slot for a trailing argument. */
            const bool isEntryReturnAddress =
                chunk.location().domain() == MemoryDomain::STACK &&
                chunk.location().addr() == 0 &&
                dflow::isReturnAddress(term, dataflow);
            if (!isEntryReturnAddress && intersect(term, chunk.location())) {
                bool used = false;
                foreach (const auto &use, uses.getUses(term)) {
                    if (intersect(use.term(), use.location())) {
                        used = true;
                        break;
                    }
                }
                if (!used) {
                    if (auto memoryLocation = fixer.removeStackOffset(chunk.location())) {
                        result.push_back(memoryLocation);
                    }
                }
            }
        }
    }

    /*
     * A direct cdecl cleanup is stronger evidence than the speculative
     * reaching-definition heuristic. Keep only the stack words that the
     * caller demonstrably removes for this particular call.
     */
    if (auto cleanupSize = getCallerCleanupSize(call, convention)) {
        const BitAddr begin = convention->firstArgumentOffset();
        const BitAddr end = begin + *cleanupSize * CHAR_BIT;
        result.erase(
            std::remove_if(result.begin(), result.end(),
                [&](const MemoryLocation &location) {
                    return location.domain() != MemoryDomain::STACK ||
                           location.addr() < begin || location.endAddr() > end;
                }),
            result.end());
    }

    return result;
}

std::vector<MemoryLocation> SignatureAnalyzer::getUsedReturnValueLocations(const Call *call) {
    assert(call != nullptr);

    std::vector<MemoryLocation> result;

    auto callHook = hooks_.getCallHook(call);
    auto function = call->basicBlock()->function();
    auto &uses = *function2uses_.at(function);

    foreach (const auto &locationAndTerm, callHook->speculativeReturnValueTerms()) {
        MemoryLocation usedPart;

        foreach (const auto &use, uses.getUses(locationAndTerm.second)) {
            usedPart.merge(intersect(use.term(), use.location()));
        }

        if (usedPart && usedPart.addr() == locationAndTerm.first.addr()) {
            result.push_back(usedPart);
        }
    }

    return result;
}

std::vector<MemoryLocation> SignatureAnalyzer::getUnusedReturnValueLocations(const Jump *jump) {
    assert(jump != nullptr);

    std::vector<MemoryLocation> result;

    auto returnHook = hooks_.getReturnHook(jump);
    auto function = jump->basicBlock()->function();
    auto &dataflow = *dataflows_.at(function);
    auto &uses = *function2uses_.at(function);
    auto &liveness = *livenesses_.at(function);

    foreach (const auto &locationAndTerm, returnHook->speculativeReturnValueTerms()) {
        MemoryLocation unusedPart;

        foreach (const auto &chunk, dataflow.getDefinitions(locationAndTerm.second).chunks()) {
            foreach (const Term *definition, chunk.definitions()) {
                if (auto intersection = intersect(definition, chunk.location())) {
                    bool used = false;
                    foreach (const auto &use, uses.getUses(definition)) {
                        if (use.term() != locationAndTerm.second && intersect(use.term(), use.location()) &&
                            liveness.isLive(use.term()))
                        {
                            used = true;
                            break;
                        }
                    }
                    if (!used) {
                        unusedPart.merge(intersection);
                    }
                }
            }
        }

        if (unusedPart && unusedPart.addr() == locationAndTerm.first.addr()) {
            result.push_back(unusedPart);
        }
    }

    return result;
}

MemoryLocation SignatureAnalyzer::intersect(const Term *term, const MemoryLocation &memoryLocation) {
    assert(term);
    assert(memoryLocation);

    if (auto calleeId = nc::find(speculativeReturnValueTerm2calleeId_, term)) {
        return MemoryLocation::intersect(nc::find(id2returnValue_, calleeId), memoryLocation);
    } else {
        return memoryLocation;
    }
}

void SignatureAnalyzer::computeSignatures() {
    foreach (const auto &calleeId, id2referrers_ | boost::adaptors::map_keys) {
        computeSignatures(calleeId);
        canceled_.poll();
    }
}

namespace {

class ArgumentFactory {
    MemoryLocation stackPointer_;
public:

    ArgumentFactory(const Convention *convention) {
        if (convention) {
            stackPointer_ = convention->stackPointer();
        }
    }

    std::shared_ptr<Term> operator()(const MemoryLocation &memoryLocation) const {
        if (memoryLocation.domain() == MemoryDomain::STACK) {
            if (stackPointer_) {
                return std::make_shared<Dereference>(
                    std::make_unique<BinaryOperator>(
                        BinaryOperator::ADD,
                        std::make_unique<MemoryLocationAccess>(stackPointer_),
                        std::make_unique<Constant>(SizedValue(
                            stackPointer_.size<SmallBitSize>(),
                            memoryLocation.addr() / CHAR_BIT)),
                        stackPointer_.size<SmallBitSize>()),
                    MemoryDomain::MEMORY,
                    memoryLocation.size<SmallBitSize>()
                );
            } else {
                return nullptr;
            }
        } else {
            return std::make_shared<MemoryLocationAccess>(memoryLocation);
        }
    }
};

} // anonymous namespace

void SignatureAnalyzer::computeSignatures(const CalleeId &calleeId) {
    assert(calleeId);

    auto functionSignature = std::make_shared<FunctionSignature>();
    auto convention = hooks_.conventions().getConvention(calleeId);
    auto argumentFactory = ArgumentFactory(convention);

    foreach (const auto &memoryLocation, nc::find(id2arguments_, calleeId)) {
        if (auto term = argumentFactory(memoryLocation)) {
            functionSignature->arguments().push_back(term);
        }
    }

    if (auto &returnValueLocation = nc::find(id2returnValue_, calleeId)) {
        functionSignature->setReturnValue(std::make_shared<MemoryLocationAccess>(returnValueLocation));
    }

    if (calleeId.entryAddress()) {
        signatures_.setSignature(*calleeId.entryAddress(), functionSignature);
    }

    const auto &referrers = nc::find(id2referrers_, calleeId);
    foreach (auto function, referrers.functions) {
        signatures_.setSignature(function, functionSignature);
    }

    foreach (auto call, referrers.calls) {
        auto callSignature = std::make_shared<CallSignature>();

        callSignature->arguments() = functionSignature->arguments();
        foreach (const auto &memoryLocation, nc::find(call2extraArguments_, call)) {
            if (auto term = argumentFactory(memoryLocation)) {
                callSignature->arguments().push_back(term);
                functionSignature->setVariadic();
            }
        }
        callSignature->setReturnValue(functionSignature->returnValue());
        callSignature->setPrototype(functionSignature->prototype());

        signatures_.setSignature(call, callSignature);
    }
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
