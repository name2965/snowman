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
#include "CallFrameAnalyzer.h"
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

CalleeId SignatureAnalyzer::getAnalysisCalleeId(
        const Call *call, const dflow::Dataflow &dataflow) const {
    assert(call != nullptr);
    if (call->instruction()) {
        const CalleeId callSiteId(
            CallAddress(call->instruction()->addr()));
        if (hooks_.conventions().getConvention(callSiteId) &&
            !hooks_.conventions().isFallbackConvention(callSiteId))
        {
            return callSiteId;
        }
    }
    return getCalleeId(call, dataflow);
}

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

        /* Signature reconstruction turns dataflow facts into an ABI contract
         * used by a later analysis run.  Never promote a bounded,
         * non-converged intermediate state into that persistent contract. */
        if (!dataflow.converged()) {
            continue;
        }

        id2referrers_[getCalleeId(function)].functions.push_back(function);

        foreach (auto basicBlock, function->basicBlocks()) {
            foreach (auto statement, basicBlock->statements()) {
                if (auto call = statement->asCall()) {
                    const CalleeId id =
                        getAnalysisCalleeId(call, dataflow);

                    id2referrers_[id].calls.push_back(call);
                    function2calls_[function].push_back(call);

                    const CallHook *callHook = hooks_.getCallHook(call);
                    foreach (const Term *term,
                             callHook->observedArgumentTerms()) {
                        function2observedCallArgumentTerms_[function].insert(
                            term);
                    }
                    foreach (const auto &locationAndTerm, callHook->speculativeReturnValueTerms()) {
                        speculativeReturnValueTerm2calleeId_[locationAndTerm.second] = id;
                    }
                } else if (auto jump = statement->asJump()) {
                    if (dflow::isReturn(jump, dataflow)) {
                        auto id = getCalleeId(function);

                        id2referrers_[id].returns.push_back(jump);
                        function2returns_[function].push_back(jump);

                        const ReturnHook *returnHook =
                            hooks_.getReturnHook(jump);
                        foreach (const Term *term,
                                 returnHook->observedReturnValueTerms()) {
                            function2observedReturnValueTerms_[function].insert(
                                term);
                        }
                        foreach (const auto &locationAndTerm, returnHook->speculativeReturnValueTerms()) {
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

boost::optional<std::size_t> getVariadicFixedArgumentCount(
        const Signatures &signatures, const Call *call) {
    const auto &signature = signatures.getSignature(
        call, SignatureSource::EXTERNAL);
    const auto &prototype = signature ? signature->prototype() :
                                        std::shared_ptr<const FunctionPrototype>();
    if (!prototype || !prototype->variadic() ||
        signature->arguments().size() < prototype->parameters().size())
    {
        return boost::none;
    }
    return prototype->parameters().size();
}

bool makeScalarFixedArgumentPrefix(
        const Convention &convention, std::size_t fixedArgumentCount,
        std::vector<MemoryLocation> &result) {
    result.clear();
    result.reserve(fixedArgumentCount);

    const auto &groups = convention.argumentGroups();
    const std::vector<MemoryLocation> *registerArguments =
        groups.empty() ? nullptr : &groups.front();
    const std::size_t registerArgumentCount =
        registerArguments ? registerArguments->size() : 0;
    const std::size_t fixedRegisterCount =
        std::min(fixedArgumentCount, registerArgumentCount);
    for (std::size_t index = 0; index < fixedRegisterCount; ++index) {
        result.push_back((*registerArguments)[index]);
    }

    const std::size_t fixedStackCount =
        fixedArgumentCount - fixedRegisterCount;
    if (fixedStackCount == 0) {
        return true;
    }

    const BitSize firstOffset = convention.firstArgumentOffset();
    const BitSize alignment = convention.argumentAlignment();
    if (firstOffset < 0 || alignment <= 0 ||
        static_cast<ConstantValue>(fixedStackCount - 1) >
            static_cast<ConstantValue>(
                ((std::numeric_limits<BitSize>::max)() - firstOffset) /
                alignment))
    {
        result.clear();
        return false;
    }
    for (std::size_t index = 0; index < fixedStackCount; ++index) {
        result.push_back(MemoryLocation(
            MemoryDomain::STACK,
            firstOffset + static_cast<BitSize>(index) * alignment,
            alignment));
    }
    return true;
}

std::vector<MemoryLocation> sortVariadicTailArguments(
        const Convention &convention,
        std::vector<MemoryLocation> arguments,
        const boost::optional<std::size_t> &fixedArgumentCount) {
    if (!fixedArgumentCount) {
        return convention.sortArguments(std::move(arguments));
    }

    /* sortArguments intentionally rejects a suffix after a gap. An external
     * variadic prototype supplies exactly the missing fixed prefix, while the
     * inferred snapshot contains only the tail. Add ABI-slot placeholders for
     * sorting, then remove them from the inferred result. Schema-v1 external
     * prototypes contain only scalar integer/pointer parameters, so the first
     * convention group and one aligned stack slot per remaining parameter are
     * the complete fixed-prefix layout. */
    std::vector<MemoryLocation> prefix;
    if (!makeScalarFixedArgumentPrefix(
            convention, *fixedArgumentCount, prefix))
    {
        return convention.sortArguments(std::move(arguments));
    }
    arguments.insert(arguments.end(), prefix.begin(), prefix.end());
    arguments = convention.sortArguments(std::move(arguments));
    arguments.erase(
        std::remove_if(arguments.begin(), arguments.end(),
            [&](const MemoryLocation &location) {
                return nc::contains(prefix, location);
            }),
        arguments.end());
    return arguments;
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

    auto getArgumentLocation = [&](const Placement &placement) -> MemoryLocation {
        if (placement.inFunctions) {
            return placement.inFunctions;
        } else if (!placement.inCalls.empty() &&
                   placement.inCalls.size() == referrers.calls.size() &&
                   isHomogeneous(
                       placement.inCalls | boost::adaptors::map_values)) {
            /* Call-site evidence is a common formal only when every known
             * call supplies the slot.  Otherwise a long variadic call would
             * promote its trailing slots into shorter calls. */
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

    boost::optional<std::size_t> commonVariadicFixedArgumentCount;
    bool commonVariadicPrefix = !referrers.calls.empty();
    foreach (const Call *call, referrers.calls) {
        const auto fixedArgumentCount =
            getVariadicFixedArgumentCount(signatures_, call);
        if (!fixedArgumentCount ||
            (commonVariadicFixedArgumentCount &&
             *commonVariadicFixedArgumentCount != *fixedArgumentCount))
        {
            commonVariadicPrefix = false;
            break;
        }
        commonVariadicFixedArgumentCount = fixedArgumentCount;
    }
    if (!commonVariadicPrefix) {
        commonVariadicFixedArgumentCount = boost::none;
    }
    arguments = sortVariadicTailArguments(
        *convention, std::move(arguments),
        commonVariadicFixedArgumentCount);

    foreach (auto &callAndLocations, extraArguments) {
        auto &callArguments = callAndLocations.second;
        callArguments.insert(callArguments.end(), arguments.begin(), arguments.end());
        callArguments = sortVariadicTailArguments(
            *convention, std::move(callArguments),
            getVariadicFixedArgumentCount(
                signatures_, callAndLocations.first));
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

    /* Replace the per-call set as a whole. A location can move from
     * call-specific to common during the fixpoint; retaining its old entry
     * would make that stale argument survive in the final signature. */
    foreach (const Call *call, referrers.calls) {
        auto newArguments = extraArguments.find(call);
        auto oldExtraArguments = call2extraArguments_.find(call);
        if (newArguments == extraArguments.end() ||
            newArguments->second.empty())
        {
            if (oldExtraArguments != call2extraArguments_.end()) {
                call2extraArguments_.erase(oldExtraArguments);
                changed = true;
            }
        } else if (oldExtraArguments == call2extraArguments_.end() ||
                   oldExtraArguments->second != newArguments->second)
        {
            call2extraArguments_[call] =
                std::move(newArguments->second);
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

bool checkedScaleByteOffset(SignedConstantValue offset, BitAddr &result) {
    if (offset < (std::numeric_limits<BitAddr>::min)() / CHAR_BIT ||
        offset > (std::numeric_limits<BitAddr>::max)() / CHAR_BIT)
    {
        return false;
    }
    result = offset * CHAR_BIT;
    return true;
}

bool checkedShiftLocation(const MemoryLocation &location, BitSize offset,
                          MemoryLocation &result) {
    if (!location) {
        return false;
    }
    const BitAddr minimum = (std::numeric_limits<BitAddr>::min)();
    const BitAddr maximumStart =
        (std::numeric_limits<BitAddr>::max)() - location.size();
    if ((offset > 0 && location.addr() > maximumStart - offset) ||
        (offset < 0 && (offset == minimum ||
                        location.addr() < minimum - offset)))
    {
        return false;
    }
    const BitAddr address = location.addr() + offset;
    if (address < minimum || address > maximumStart) {
        return false;
    }
    result = MemoryLocation(location.domain(), address, location.size());
    return true;
}

class StackOffsetFixer {
    boost::optional<BitSize> stackOffset_;

public:
    StackOffsetFixer(const Term *stackPointer, const dflow::Dataflow &dataflow) {
        if (stackPointer) {
            const dflow::Value *value = dataflow.findValue(stackPointer);
            BitAddr offset;
            if (value && value->isStackOffset() &&
                checkedScaleByteOffset(value->stackOffset(), offset))
            {
                stackOffset_ = offset;
            }
        }
    }

    MemoryLocation addStackOffset(const MemoryLocation &memoryLocation) {
        if (memoryLocation.domain() == MemoryDomain::STACK) {
            if (stackOffset_) {
                MemoryLocation result;
                return checkedShiftLocation(
                    memoryLocation, *stackOffset_, result) ?
                    result : MemoryLocation();
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
                if (*stackOffset_ ==
                    (std::numeric_limits<BitSize>::min)())
                {
                    return MemoryLocation();
                }
                MemoryLocation result;
                return checkedShiftLocation(
                    memoryLocation, -*stackOffset_, result) ?
                    result : MemoryLocation();
            } else {
                return MemoryLocation();
            }
        } else {
            return memoryLocation;
        }
    }
};

/** Removes an exact byte/bit interval from a set of disjoint candidate
 * intervals.  A wide machine write can feed independent consumers through
 * different subranges, so definition-wide used/unused booleans are not a
 * sufficiently precise abstraction here. */
void subtractLocation(
        std::vector<MemoryLocation> &parts,
        const MemoryLocation &excluded) {
    std::vector<MemoryLocation> result;
    result.reserve(parts.size() + 1);
    foreach (const MemoryLocation &part, parts) {
        const MemoryLocation overlap =
            MemoryLocation::intersect(part, excluded);
        if (!overlap) {
            result.push_back(part);
            continue;
        }
        if (part.addr() < overlap.addr()) {
            result.push_back(MemoryLocation(
                part.domain(), part.addr(),
                overlap.addr() - part.addr()));
        }
        if (overlap.endAddr() < part.endAddr()) {
            result.push_back(MemoryLocation(
                part.domain(), overlap.endAddr(),
                part.endAddr() - overlap.endAddr()));
        }
    }
    parts.swap(result);
}

/**
 * Appends the parts of a read whose value can come from the function's
 * incoming machine state.
 *
 * Reaching-definition chunks describe bit coverage.  A gap means that no
 * definition in the function reaches that part, while an explicit incoming
 * marker means that only some CFG alternatives define it.  An unknown-write
 * marker is deliberately not treated as a formal argument: it represents an
 * operation inside the function whose value merely is not modelled.
 */
void appendIncomingParts(
        const MemoryLocation &location,
        const dflow::ReachingDefinitions &definitions,
        const EntryHook *entryHook,
        std::vector<MemoryLocation> &result) {
    if (!location) {
        return;
    }

    BitAddr coveredUntil = location.addr();
    foreach (const dflow::ReachingDefinitions::Chunk &chunk,
             definitions.chunks()) {
        const MemoryLocation overlap =
            MemoryLocation::intersect(location, chunk.location());
        if (!overlap) {
            continue;
        }

        if (coveredUntil < overlap.addr()) {
            result.push_back(MemoryLocation(
                location.domain(), coveredUntil,
                overlap.addr() - coveredUntil));
        }
        bool hasObservedEntryDefinition = false;
        if (entryHook) {
            foreach (const Term *definition, chunk.definitions()) {
                if (entryHook->isObservedArgumentTerm(definition)) {
                    hasObservedEntryDefinition = true;
                    break;
                }
            }
        }
        if (chunk.hasIncomingDefinition() || hasObservedEntryDefinition) {
            result.push_back(overlap);
        }
        if (overlap.endAddr() > coveredUntil) {
            coveredUntil = overlap.endAddr();
        }
    }

    if (coveredUntil < location.endAddr()) {
        result.push_back(MemoryLocation(
            location.domain(), coveredUntil,
            location.endAddr() - coveredUntil));
    }
}

} // anonymous namespace

std::vector<MemoryLocation> SignatureAnalyzer::getUndefinedUses(const Function *function) {
    assert(function != nullptr);

    auto &dataflow = *dataflows_.at(function);

    std::vector<MemoryLocation> result;
    if (!dataflow.converged()) {
        /* Partial fixpoint facts can manufacture both missing and concrete
         * definitions depending on block order.  Neither is signature
         * evidence. */
        return result;
    }
    const EntryHook *entryHook = hooks_.getEntryHook(function);
    const auto &observedCallArgumentTerms = nc::find(
        function2observedCallArgumentTerms_, function);
    const auto &observedReturnValueTerms = nc::find(
        function2observedReturnValueTerms_, function);

    /*
     * If a term reads a memory location through which an argument
     * can be passed, and nobody defines this memory location, this
     * location is likely to be actually used for passing an argument.
     */
    foreach (const auto &termAndLocation, dataflow.term2location()) {
        auto term = termAndLocation.first;
        const auto &memoryLocation = termAndLocation.second;

        /* Inference probes are not source-level consumers. In particular, a
         * variadic-tail probe with no caller store must not become a formal
         * input and then feed itself through the next pass's EntryHook. Fixed
         * authoritative argument reads are deliberately absent from these
         * registries and remain valid evidence. */
        if (memoryLocation && term->isRead() &&
            !nc::contains(observedCallArgumentTerms, term) &&
            !nc::contains(observedReturnValueTerms, term))
        {
            const MemoryLocation usedPart = intersect(term, memoryLocation);
            if (usedPart) {
                appendIncomingParts(
                    usedPart,
                    dataflow.getDefinitions(term).projected(usedPart),
                    entryHook,
                    result);
            }
        }
    }

    /*
     * If a call has an argument whose memory location can be used
     * for passing arguments to this function, and this memory location
     * is not defined in the function, this memory location is likely
     * to be used for passing an argument.
     */
    foreach (auto call, nc::find(function2calls_, function)) {
        const auto &callArguments = nc::find(
            id2arguments_, getAnalysisCalleeId(call, dataflow));
        if (callArguments.empty()) {
            continue;
        }

        auto callHook = hooks_.getCallHook(call);
        if (!callHook || !callHook->snapshotStatement()) {
            continue;
        }
        auto fixer = StackOffsetFixer(callHook->stackPointer(), dataflow);
        auto &reachingDefinitions = dataflow.getDefinitions(callHook->snapshotStatement());

        foreach (auto memoryLocation, callArguments) {
            memoryLocation = fixer.addStackOffset(memoryLocation);

            if (memoryLocation) {
                appendIncomingParts(
                    memoryLocation,
                    reachingDefinitions.projected(memoryLocation), entryHook,
                    result);
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
    if (!callHook || !callHook->snapshotStatement()) {
        return result;
    }
    auto function = call->basicBlock()->function();
    auto &dataflow = *dataflows_.at(function);
    if (!dataflow.converged()) {
        return result;
    }
    auto &uses = *function2uses_.at(function);
    auto fixer = StackOffsetFixer(callHook->stackPointer(), dataflow);
    const auto &observedCallArgumentTerms = nc::find(
        function2observedCallArgumentTerms_, function);

    const CalleeId calleeId = getAnalysisCalleeId(call, dataflow);
    CalleeId callSiteId;
    if (call->instruction()) {
        callSiteId = CalleeId(CallAddress(call->instruction()->addr()));
    }
    const bool hasCallSiteConvention = callSiteId &&
        hooks_.conventions().getConvention(callSiteId) &&
        !hooks_.conventions().isFallbackConvention(callSiteId);
    boost::optional<ByteSize> stackArgumentsSize =
        hasCallSiteConvention ?
            hooks_.conventions().getStackArgumentsSize(callSiteId) :
            hooks_.conventions().getStackArgumentsSize(calleeId);

    /* A resolved address can be shared by forwarded imports with distinct
     * source contracts. Once a call-site convention exists, never combine it
     * with the target body's stack effect or extent. */
    ReturnStackCleanup returnCleanup = hasCallSiteConvention ?
        hooks_.conventions().getReturnStackCleanup(callSiteId) :
        hooks_.conventions().getReturnStackCleanup(calleeId);
    if (returnCleanup.isExact() && convention->stackPointer() &&
        convention->firstArgumentOffset() ==
            convention->stackPointer().size())
    {
        const ByteSize cleanupSize = returnCleanup.size();
        const bool cleanupDefinesExtent =
            cleanupSize > 0 || convention->calleeCleanup();
        if (cleanupDefinesExtent) {
            if (stackArgumentsSize && *stackArgumentsSize != cleanupSize) {
                /* Provider/decorated-name metadata and the executable body
                 * disagree. Neither is a sound argument bound on its own. */
                stackArgumentsSize = boost::none;
            } else {
                stackArgumentsSize = cleanupSize;
            }
        }
    }

    /* A body-less external cdecl call has no callee-side reads from which to
     * reconstruct stack parameters.  Accept caller evidence only when the
     * call-frame analysis proves a complete push/restore extent.  This stays
     * call-site-local: it does not relabel the target's calling convention or
     * manufacture a callee cleanup effect. */
    const auto &referrers = nc::find(id2referrers_, calleeId);
    const bool implementationBodyUnavailable =
        referrers.functions.empty() ||
        hooks_.conventions().isExternalBodyOpaque(calleeId);
    if (!stackArgumentsSize && returnCleanup.isUnknown() &&
        implementationBodyUnavailable)
    {
        stackArgumentsSize =
            CallFrameAnalyzer::inferCallerCleanupArgumentSize(
                call, convention, callHook, dataflow);
    }

    /* An authoritative variadic prototype deliberately has no fixed total
     * stack extent.  Once a tail slot has been observed, the external call
     * hook carries that slot into the next semantic pass so it can be
     * revalidated.  Remember only locations for which a real reaching
     * definition still feeds that synthetic tail read.  This is a whitelist,
     * not fresh argument evidence: it cannot manufacture a new stack
     * argument, and a removed or overwritten store disappears immediately.
     *
     * Do not apply the rule to wholly inferred signatures.  Without an
     * authoritative variadic fixed prefix, retaining every previous stack
     * candidate would make a local dead store self-sustaining after the
     * original frame-extent proof vanished. */
    std::vector<MemoryLocation> revalidatedVariadicStackParts;
    foreach (const auto &chunk, dataflow.getDefinitions(callHook->snapshotStatement()).chunks()) {
        foreach (const Term *term, chunk.definitions()) {
            /* Do not mistake the caller's own return-address slot for a trailing argument. */
            const bool isEntryReturnAddress =
                chunk.location().domain() == MemoryDomain::STACK &&
                chunk.location().addr() == 0 &&
                dflow::isReturnAddress(term, dataflow);
            const MemoryLocation definedPart =
                intersect(term, chunk.location());
            if (!isEntryReturnAddress && definedPart) {
                std::vector<MemoryLocation> unusedParts(1, definedPart);
                std::vector<MemoryLocation> observedVariadicTailParts;
                foreach (const auto &use, uses.getUses(term)) {
                    const MemoryLocation usedPart =
                        MemoryLocation::intersect(
                            definedPart, use.location());
                    if (!usedPart) {
                        continue;
                    }
                    const MemoryLocation effectiveUsedPart =
                        intersect(use.term(), usedPart);
                    if (!effectiveUsedPart) {
                        continue;
                    }
                    if (callHook->isObservedArgumentTerm(use.term())) {
                        if (callHook->argumentObservation() ==
                                CallHook::ArgumentObservation::VARIADIC_TAIL)
                        {
                            observedVariadicTailParts.push_back(
                                effectiveUsedPart);
                        }
                    } else if (nc::contains(
                                   observedCallArgumentTerms,
                                   use.term()))
                    {
                        /* This is an inference probe owned by a different call
                         * site in the same function, not a real consumer. */
                        continue;
                    } else {
                        /* A single wide definition can supply a fixed argument
                         * and an independent variadic tail slot. Remove only
                         * the subrange consumed by the non-tail use. */
                        subtractLocation(
                            unusedParts, effectiveUsedPart);
                        if (unusedParts.empty()) {
                            break;
                        }
                    }
                }
                foreach (const MemoryLocation &unusedPart, unusedParts) {
                    if (auto memoryLocation =
                            fixer.removeStackOffset(unusedPart))
                    {
                        result.push_back(memoryLocation);
                        if (!observedVariadicTailParts.empty() &&
                            memoryLocation.domain() == MemoryDomain::STACK)
                        {
                            foreach (const MemoryLocation &tailPart,
                                     observedVariadicTailParts) {
                                const MemoryLocation retainedTailPart =
                                    MemoryLocation::intersect(
                                        unusedPart, tailPart);
                                const MemoryLocation normalizedTailPart =
                                    retainedTailPart ?
                                    fixer.removeStackOffset(
                                        retainedTailPart) :
                                    MemoryLocation();
                                if (normalizedTailPart) {
                                    revalidatedVariadicStackParts.push_back(
                                        normalizedTailPart);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /*
     * Dead stores alone do not prove that a stack slot is an argument: a
     * caller local can occupy the same relative offset. Keep stack candidates
     * only inside an extent proved by ABI metadata or a uniform callee return
     * effect. A caller-side SP discard is merely an upper bound: compilers can
     * fold local-frame teardown into the instruction following a call, so it
     * must not be reinterpreted as a callee argument count.
     */
    BitAddr stackArgumentsEnd = 0;
    bool validStackExtent = false;
    if (stackArgumentsSize && *stackArgumentsSize >= 0 &&
        convention->firstArgumentOffset() >= 0 &&
        convention->firstArgumentOffset() % CHAR_BIT == 0 &&
        convention->argumentAlignment() > 0 &&
        convention->argumentAlignment() % CHAR_BIT == 0 &&
        *stackArgumentsSize <=
            ((std::numeric_limits<BitAddr>::max)() -
             convention->firstArgumentOffset()) / CHAR_BIT)
    {
        stackArgumentsEnd = convention->firstArgumentOffset() +
            *stackArgumentsSize * CHAR_BIT;
        validStackExtent = true;
    }
    std::vector<MemoryLocation> boundedResult;
    foreach (const MemoryLocation &location, result) {
        if (location.domain() != MemoryDomain::STACK) {
            boundedResult.push_back(location);
            continue;
        }
        if (validStackExtent) {
            if (location.addr() >= convention->firstArgumentOffset() &&
                location.addr() <= stackArgumentsEnd &&
                /* Avoid MemoryLocation::endAddr(): malformed/extreme input
                 * must not turn a signed overflow into an accepted extent. */
                location.size() <= stackArgumentsEnd - location.addr())
            {
                boundedResult.push_back(location);
            }
            continue;
        }

        /* Preserve exactly the part still consumed by a previously observed
         * variadic tail. A wide reaching definition can span unrelated
         * locals or fixed parameters, so retaining its whole chunk would
         * turn partial historical evidence into new arguments. */
        foreach (const MemoryLocation &tailPart,
                 revalidatedVariadicStackParts) {
            const MemoryLocation overlap =
                MemoryLocation::intersect(location, tailPart);
            if (overlap) {
                boundedResult.push_back(overlap);
            }
        }
    }
    result.swap(boundedResult);

    return result;
}

std::vector<MemoryLocation> SignatureAnalyzer::getUsedReturnValueLocations(const Call *call) {
    assert(call != nullptr);

    std::vector<MemoryLocation> result;

    const Function *function = call->basicBlock()->function();
    const dflow::Dataflow &dataflow = *dataflows_.at(function);
    if (!dataflow.converged()) {
        return result;
    }

    auto callHook = hooks_.getCallHook(call);
    auto &uses = *function2uses_.at(function);

    foreach (const auto &locationAndTerm, callHook->speculativeReturnValueTerms()) {
        std::vector<MemoryLocation> usedParts;

        foreach (const auto &use, uses.getUses(locationAndTerm.second)) {
            const MemoryLocation usedPart = MemoryLocation::intersect(
                locationAndTerm.first,
                intersect(use.term(), use.location()));
            if (usedPart) {
                usedParts.push_back(usedPart);
            }
        }

        std::sort(usedParts.begin(), usedParts.end());
        BitAddr contiguousEnd = locationAndTerm.first.addr();
        foreach (const MemoryLocation &usedPart, usedParts) {
            if (usedPart.endAddr() <= contiguousEnd) {
                continue;
            }
            if (usedPart.addr() > contiguousEnd) {
                break;
            }
            contiguousEnd = usedPart.endAddr();
        }
        if (contiguousEnd > locationAndTerm.first.addr()) {
            result.push_back(MemoryLocation(
                locationAndTerm.first.domain(),
                locationAndTerm.first.addr(),
                contiguousEnd - locationAndTerm.first.addr()));
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
    if (!dataflow.converged()) {
        return result;
    }
    auto &uses = *function2uses_.at(function);
    auto &liveness = *livenesses_.at(function);
    const auto &observedReturnValueTerms = nc::find(
        function2observedReturnValueTerms_, function);

    foreach (const auto &locationAndTerm, returnHook->speculativeReturnValueTerms()) {
        std::vector<MemoryLocation> unusedParts;

        foreach (const auto &chunk, dataflow.getDefinitions(locationAndTerm.second).chunks()) {
            foreach (const Term *definition, chunk.definitions()) {
                if (auto intersection = intersect(definition, chunk.location())) {
                    std::vector<MemoryLocation> definitionUnusedParts(
                        1, intersection);
                    foreach (const auto &use, uses.getUses(definition)) {
                        if (use.term() == locationAndTerm.second ||
                            nc::contains(observedReturnValueTerms,
                                         use.term()) ||
                            !liveness.isLive(use.term()))
                        {
                            continue;
                        }
                        const MemoryLocation usedPart =
                            MemoryLocation::intersect(
                                intersection, use.location());
                        if (!usedPart) {
                            continue;
                        }
                        const MemoryLocation liveUsedPart =
                            intersect(use.term(), usedPart);
                        if (liveUsedPart) {
                            subtractLocation(
                                definitionUnusedParts, liveUsedPart);
                            if (definitionUnusedParts.empty()) {
                                break;
                            }
                        }
                    }
                    unusedParts.insert(
                        unusedParts.end(),
                        definitionUnusedParts.begin(),
                        definitionUnusedParts.end());
                }
            }
        }

        /* Return values are a contiguous ABI prefix. Sort and coalesce only
         * adjacent/overlapping unused pieces starting at the declared return
         * location; never bridge a live middle subrange. */
        std::sort(unusedParts.begin(), unusedParts.end());
        BitAddr contiguousEnd = locationAndTerm.first.addr();
        foreach (const MemoryLocation &unusedPart, unusedParts) {
            const MemoryLocation candidate = MemoryLocation::intersect(
                unusedPart, locationAndTerm.first);
            if (!candidate || candidate.endAddr() <= contiguousEnd) {
                continue;
            }
            if (candidate.addr() > contiguousEnd) {
                break;
            }
            contiguousEnd = candidate.endAddr();
        }
        if (contiguousEnd > locationAndTerm.first.addr()) {
            result.push_back(MemoryLocation(
                locationAndTerm.first.domain(),
                locationAndTerm.first.addr(),
                contiguousEnd - locationAndTerm.first.addr()));
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

    const auto &referrers = nc::find(id2referrers_, calleeId);
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
        const auto callHook = hooks_.getCallHook(call);
        if (callHook && callHook->argumentObservation() ==
                CallHook::ArgumentObservation::VARIADIC_TAIL)
        {
            callSignature->setArgumentEvidence(
                CallSignature::ArgumentEvidence::VARIADIC_TAIL);
        }

        signatures_.setSignature(
            call, callSignature, SignatureSource::INFERRED);
    }

    /* Complete the shared function signature before publishing it. In
     * particular, extra call-site arguments above can prove variadicity.
     * Signatures keeps stable objects for semantically equal replacements,
     * so mutating a discarded candidate after insertion would otherwise lose
     * that fact and bypass its semantic revision counter. */
    if (calleeId.entryAddress()) {
        signatures_.setSignature(
            *calleeId.entryAddress(), functionSignature,
            SignatureSource::INFERRED);
    }

    foreach (auto function, referrers.functions) {
        signatures_.setSignature(
            function, functionSignature, SignatureSource::INFERRED);
    }
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
