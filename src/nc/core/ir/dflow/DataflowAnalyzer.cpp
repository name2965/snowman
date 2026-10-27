/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

//
// SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
// Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
// Alexander Fokin, Sergey Levin, Leonid Tsvetkov
//
// This file is part of SmartDec decompiler.
//
// SmartDec decompiler is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// SmartDec decompiler is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
//

#include "DataflowAnalyzer.h"

#include <climits>
#include <limits>
#include <vector>

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/CancellationToken.h>
#include <nc/common/Foreach.h>
#include <nc/common/Unreachable.h>

#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>

#include "Dataflow.h"
#include "Value.h"

namespace nc {
namespace core {
namespace ir {
namespace dflow {

namespace {

template<class Map, class Pred>
void remove_if(Map &map, Pred pred) {
    auto i = map.begin();
    auto iend = map.end();

    while (i != iend) {
        if (pred(i->first)) {
            i = map.erase(i);
        } else {
            ++i;
        }
    }
}

bool getSignedMachineOffset(ConstantValue bits, SmallBitSize size,
                            SignedConstantValue &result) {
    if (size <= 0 || size > static_cast<SmallBitSize>(
            sizeof(ConstantValue) * CHAR_BIT))
    {
        return false;
    }

    const ConstantValue mask = size == static_cast<SmallBitSize>(
            sizeof(ConstantValue) * CHAR_BIT) ?
        (std::numeric_limits<ConstantValue>::max)() :
        (ConstantValue(1) << size) - 1;
    bits &= mask;
    const ConstantValue sign = ConstantValue(1) << (size - 1);
    if ((bits & sign) == 0) {
        result = static_cast<SignedConstantValue>(bits);
        return true;
    }

    const ConstantValue magnitude = ((~bits) & mask) + 1;
    if (magnitude == ConstantValue(1) <<
            (sizeof(ConstantValue) * CHAR_BIT - 1))
    {
        result = (std::numeric_limits<SignedConstantValue>::min)();
    } else {
        result = -static_cast<SignedConstantValue>(magnitude);
    }
    return true;
}

/** Applies machine-width modular pointer arithmetic to a symbolic frame
 * offset and returns its canonical signed representative. */
bool computeStackOffset(SignedConstantValue base, ConstantValue amount,
                        SmallBitSize size, bool subtract,
                        SignedConstantValue &result) {
    if (size <= 0 || size > static_cast<SmallBitSize>(
            sizeof(ConstantValue) * CHAR_BIT))
    {
        return false;
    }

    const ConstantValue mask = size == static_cast<SmallBitSize>(
            sizeof(ConstantValue) * CHAR_BIT) ?
        (std::numeric_limits<ConstantValue>::max)() :
        (ConstantValue(1) << size) - 1;
    const ConstantValue baseBits = static_cast<ConstantValue>(base) & mask;
    const ConstantValue resultBits = subtract ?
        (baseBits - (amount & mask)) & mask :
        (baseBits + (amount & mask)) & mask;
    return getSignedMachineOffset(resultBits, size, result);
}

bool checkedByteAddressToBitAddress(ConstantValue address, BitSize size,
                                    BitAddr &result) {
    assert(size > 0);

    const BitAddr maximumStart =
        (std::numeric_limits<BitAddr>::max)() - size;
    if (address > static_cast<ConstantValue>(maximumStart) / CHAR_BIT) {
        return false;
    }
    result = static_cast<BitAddr>(address * CHAR_BIT);
    return true;
}

bool checkedStackOffsetToBitAddress(SignedConstantValue offset, BitSize size,
                                    BitAddr &result) {
    assert(size > 0);

    const BitAddr minimum = (std::numeric_limits<BitAddr>::min)();
    const BitAddr maximumStart =
        (std::numeric_limits<BitAddr>::max)() - size;
    if (offset < minimum / CHAR_BIT ||
        offset > maximumStart / CHAR_BIT)
    {
        return false;
    }
    result = offset * CHAR_BIT;
    return true;
}

bool checkedBitAddress(ConstantValue address, BitSize size, BitAddr &result) {
    assert(size > 0);

    const BitAddr maximumStart =
        (std::numeric_limits<BitAddr>::max)() - size;
    if (address > static_cast<ConstantValue>(maximumStart)) {
        return false;
    }
    result = static_cast<BitAddr>(address);
    return true;
}

/** Adds a value-less may-definition to each existing tracked interval.
 * Keeping the intervals separate avoids inventing definitions for gaps and
 * avoids address overflow when far-apart locations are present. */
void addPossibleUnknownDefinitions(
        const std::vector<MemoryLocation> &locations,
        ReachingDefinitions &definitions) {
    ReachingDefinitions possibleWrite;
    foreach (const auto &location, locations) {
        possibleWrite.addUnknownDefinition(location);
    }
    definitions.merge(possibleWrite);
}

std::vector<MemoryLocation> getAllDefinedMemoryLocations(
        const ReachingDefinitions &definitions) {
    std::vector<MemoryLocation> result;
    result.reserve(definitions.chunks().size());
    foreach (const auto &chunk, definitions.chunks()) {
        result.push_back(chunk.location());
    }
    return result;
}

bool isRegisterDomain(Domain domain) {
    return domain >= MemoryDomain::FIRST_REGISTER &&
        domain <= MemoryDomain::LAST_REGISTER;
}

/** Returns existing tracked memory intervals without inventing ranges across
 * gaps. Stack and other non-register domains can be selected independently so
 * an exact stack-derived pointer does not unnecessarily destroy global facts. */
std::vector<MemoryLocation> getDefinedNonRegisterMemoryLocations(
        const ReachingDefinitions &definitions, bool includeStack,
        bool includeOtherMemory) {
    std::vector<MemoryLocation> result;
    result.reserve(definitions.chunks().size());
    foreach (const auto &chunk, definitions.chunks()) {
        const Domain domain = chunk.location().domain();
        if (!isRegisterDomain(domain) &&
            ((domain == MemoryDomain::STACK && includeStack) ||
             (domain != MemoryDomain::STACK && includeOtherMemory)))
        {
            result.push_back(chunk.location());
        }
    }
    return result;
}

} // anonymous namespace

void DataflowAnalyzer::analyze(const CFG &cfg) {
    /* Facts from a bounded, unfinished iteration are diagnostic information,
     * not a sound basis for semantic rewrites. */
    dataflow().setAnalysisStatus(DataflowStatus::RUNNING);

    /*
     * Returns true if the given term does not cover given memory location.
     */
    auto notCovered = [this](const MemoryLocation &mloc, const Term *term) -> bool {
        return !dataflow().getMemoryLocation(term).covers(mloc);
    };

    /* Mapping of a basic block to the definitions reaching its end. */
    boost::unordered_map<const BasicBlock *, ReachingDefinitions> outDefinitions;

    /* An empty definition set is a valid abstract state.  Keep its presence
     * separate from the map's default value so a not-yet-visited predecessor
     * is not mistaken for a real path carrying the function-entry value. */
    boost::unordered_set<const BasicBlock *> initializedBlocks;

    /*
     * Running abstract interpretation until reaching a fixpoint several times in a row.
     */
    int niterations = 0;
    int nfixpoints = 0;
    const std::size_t blockCount = cfg.basicBlocks().size();
    const std::size_t maximumScalableBlockCount =
        static_cast<std::size_t>(((std::numeric_limits<int>::max)() - 3) / 4);
    const int scaledIterationLimit = blockCount > maximumScalableBlockCount ?
        (std::numeric_limits<int>::max)() :
        static_cast<int>(blockCount * 4 + 3);
    const int iterationLimit = scaledIterationLimit < 30 ?
        30 : scaledIterationLimit;

    while (nfixpoints < 3) {
        ++nfixpoints;
        const std::size_t memoryLocationRevision =
            dataflow().memoryLocationRevision();
        const std::size_t valueRevision = dataflow().valueRevision();

        /*
         * Run abstract interpretation on all basic blocks.
         */
        foreach (auto basicBlock, cfg.basicBlocks()) {
            ReachingDefinitions definitions;

            const Function *function = basicBlock->function();
            const bool isFunctionEntry =
                function && function->entry() == basicBlock;
            const auto &predecessors = cfg.getPredecessors(basicBlock);

            /* The function entry has an implicit predecessor representing
             * invocation from the caller.  Seeding that empty alternative is
             * essential when a loop has a back edge to the entry block. */
            bool hasAlternative = isFunctionEntry || predecessors.empty();

            /* Merge reaching definitions from predecessors. */
            foreach (const BasicBlock *predecessor, predecessors) {
                if (initializedBlocks.find(predecessor) ==
                    initializedBlocks.end())
                {
                    continue;
                }

                const auto position = outDefinitions.find(predecessor);
                assert(position != outDefinitions.end());
                if (hasAlternative) {
                    definitions.joinAlternative(position->second);
                } else {
                    definitions = position->second;
                    hasAlternative = true;
                }
            }

            /* A reachable predecessor must be evaluated before its successor.
             * Otherwise the absence of a map entry would become a fictitious
             * incoming-value path and could permanently poison provenance. */
            if (!hasAlternative) {
                continue;
            }

            /* Remove definitions that do not cover the memory location that they define. */
            definitions.filterOut(notCovered);

            /* Execute all the statements in the basic block. */
            foreach (auto statement, basicBlock->statements()) {
                execute(statement, definitions);
            }

            /* Something has changed? */
            ReachingDefinitions &oldDefinitions(outDefinitions[basicBlock]);
            if (oldDefinitions != definitions) {
                oldDefinitions = std::move(definitions);
                nfixpoints = 0;
            }
            if (initializedBlocks.insert(basicBlock).second) {
                nfixpoints = 0;
            }
        }

        /*
         * Some terms might have changed their addresses. Filter again.
         */
        foreach (auto &termAndDefinitions, dataflow().term2definitions()) {
            termAndDefinitions.second.filterOut(notCovered);
        }

        /*
         * Reaching definitions are not the only monotonic state in this
         * analysis.  In particular, a loop access can become ambiguous late
         * in a nominally stable pass.  Require another set of stable passes so
         * the resulting top value reaches blocks visited earlier in CFG order.
         */
        if (memoryLocationRevision != dataflow().memoryLocationRevision()) {
            nfixpoints = 0;
        }
        if (valueRevision != dataflow().valueRevision()) {
            nfixpoints = 0;
        }

        /*
         * Do we loop infinitely?
         */
        if (++niterations >= iterationLimit && nfixpoints < 3) {
            log_.warning(tr("%1: Fixpoint was not reached after %2 iterations.").arg(Q_FUNC_INFO).arg(niterations));
            break;
        }

        canceled_.poll();
    }

    const bool converged = nfixpoints >= 3;

    /*
     * Remove information about terms that disappeared.
     * Terms can disappear if e.g. a call is deinstrumented during the analysis.
     */
    auto disappeared = [](const Term *term){ return term->statement()->basicBlock() == nullptr; };

    std::vector<const Term *> disappearedTerms;
    foreach (const auto &termAndLocation, dataflow().term2location()) {
        if (disappeared(termAndLocation.first)) {
            disappearedTerms.push_back(termAndLocation.first);
        }
    }
    foreach (auto &termAndDefinitions, dataflow().term2definitions()) {
        termAndDefinitions.second.filterOut([disappeared](const MemoryLocation &, const Term *term) { return disappeared(term); } );
    }

    remove_if(dataflow().term2value(), disappeared);
    foreach (const Term *term, disappearedTerms) {
        dataflow().eraseMemoryLocation(term);
    }
    remove_if(dataflow().term2definitions(), disappeared);

    /* Cleanup above may invalidate bookkeeping revisions, but it only drops
     * terms which no longer belong to the analyzed CFG. */
    dataflow().setAnalysisStatus(converged ?
        DataflowStatus::CONVERGED : DataflowStatus::INCOMPLETE);
}

void DataflowAnalyzer::execute(const Statement *statement, ReachingDefinitions &definitions) {
    switch (statement->kind()) {
        case Statement::INLINE_ASSEMBLY:
            /* Without explicit clobber metadata, inline assembly may write
             * any tracked register or frame interval.  Preserve the old
             * definitions as may-reach alternatives, but never leave one as
             * the sole concrete definition after an opaque operation. */
            addPossibleUnknownDefinitions(
                getAllDefinedMemoryLocations(definitions), definitions);
            break;
        case Statement::ASSIGNMENT: {
            auto assignment = statement->asAssignment();
            computeValue(assignment->right(), definitions);
            handleWrite(assignment->left(),
                computeMemoryLocation(assignment->left(), definitions),
                definitions);
            break;
        }
        case Statement::JUMP: {
            auto jump = statement->asJump();

            if (jump->condition()) {
                computeValue(jump->condition(), definitions);
            }
            if (jump->thenTarget().address()) {
                computeValue(jump->thenTarget().address(), definitions);
            }
            if (jump->elseTarget().address()) {
                computeValue(jump->elseTarget().address(), definitions);
            }
            break;
        }
        case Statement::CALL: {
            auto call = statement->asCall();
            computeValue(call->target(), definitions);
            break;
        }
        case Statement::HALT: {
            break;
        }
        case Statement::TOUCH: {
            auto touch = statement->asTouch();
            switch (touch->accessType()) {
                case Term::READ:
                    computeValue(touch->term(), definitions);
                    break;
                case Term::WRITE:
                    handleWrite(touch->term(),
                        computeMemoryLocation(touch->term(), definitions),
                        definitions);
                    break;
                default:
                    unreachable();
            }
            break;
        }
        case Statement::CALLBACK: {
            statement->asCallback()->function()();
            break;
        }
        case Statement::REMEMBER_REACHING_DEFINITIONS: {
            dataflow_.getDefinitions(statement) = definitions;
            break;
        }
        case Statement::TRACKED_MEMORY_INVALIDATION: {
            auto invalidation = statement->as<TrackedMemoryInvalidation>();
            bool mayReachStack =
                invalidation->invalidateAllTrackedMemory();
            bool mayReachOtherMemory =
                invalidation->invalidateAllTrackedMemory();

            /* Resolve every argument before invalidating any memory fact. An
             * exact stack offset is confined to the current frame. Every
             * other value may designate global, heap, or custom tracked
             * memory; unknown/conflicting provenance may designate both. */
            foreach (const auto &term, invalidation->pointerCandidates()) {
                auto value = computeValue(term.get(), definitions);
                if (value->mayBeStackOffset()) {
                    mayReachStack = true;
                }
                if (!value->isStackOffset()) {
                    mayReachOtherMemory = true;
                }
            }

            if (mayReachStack || mayReachOtherMemory) {
                /* A boolean may-write effect carries no pointee extent.  Any
                 * narrower interval would guess an object boundary (and can
                 * leave stale definitions for an interior/ambiguous pointer),
                 * so conservatively invalidate every existing interval in
                 * each reachable non-register domain. Keep disjoint tracked
                 * objects disjoint: filling gaps would invent state and can
                 * overflow the address range. A future points-to/range effect
                 * can make this precise. */
                addPossibleUnknownDefinitions(
                    getDefinedNonRegisterMemoryLocations(
                        definitions, mayReachStack,
                        mayReachOtherMemory),
                    definitions);
            }
            break;
        }
        default:
            log_.warning(tr("%1: Unknown statement kind: %2.").arg(Q_FUNC_INFO).arg(statement->kind()));
            break;
    }
}

Value *DataflowAnalyzer::computeValue(const Term *term, const ReachingDefinitions &definitions) {
    switch (term->kind()) {
        case Term::INT_CONST: {
            auto constant = term->asConstant();
            Value *value = dataflow().getValue(constant);
            value->setAbstractValue(constant->value());
            value->makeNotStackOffset();
            value->makeNotProduct();
            value->makeNotReturnAddress();
            return value;
        }
        case Term::INTRINSIC: {
            auto intrinsic = term->asIntrinsic();
            Value *value = dataflow().getValue(intrinsic);

            switch (intrinsic->intrinsicKind()) {
                case Intrinsic::UNKNOWN: /* FALLTHROUGH */
                case Intrinsic::UNDEFINED: {
                    value->setAbstractValue(AbstractValue(term->size(), -1, -1));
                    /* An unconstrained machine value can contain an escaped
                     * frame pointer. Leave its pointer provenance unknown. */
                    value->makeNotProduct();
                    value->makeNotReturnAddress();
                    break;
                }
                case Intrinsic::ZERO_STACK_OFFSET: {
                    value->setAbstractValue(AbstractValue(term->size(), -1, -1));
                    value->makeStackOffset(0);
                    value->makeNotProduct();
                    value->makeNotReturnAddress();
                    break;
                }
                case Intrinsic::RETURN_ADDRESS: {
                    value->setAbstractValue(AbstractValue(term->size(), -1, -1));
                    value->makeNotStackOffset();
                    value->makeNotProduct();
                    value->makeReturnAddress();
                    break;
                }
                default: {
                    log_.warning(tr("%1: Unknown kind of intrinsic: %2.").arg(Q_FUNC_INFO).arg(intrinsic->intrinsicKind()));
                    break;
                }
            }
            return value;
        }
        case Term::MEMORY_LOCATION_ACCESS: /* FALLTHROUGH */
        case Term::DEREFERENCE: {
            const auto &memoryLocation = computeMemoryLocation(term, definitions);
            const auto &reachingDefinitions = computeReachingDefinitions(term, memoryLocation, definitions);
            return computeValue(term, memoryLocation, reachingDefinitions);
        }
        case Term::UNARY_OPERATOR:
            return computeValue(term->asUnaryOperator(), definitions);
        case Term::BINARY_OPERATOR:
            return computeValue(term->asBinaryOperator(), definitions);
        default: {
            log_.warning(tr("%1: Unknown term kind: %2.").arg(Q_FUNC_INFO).arg(term->kind()));
            return dataflow().getValue(term);
        }
    }
}

const MemoryLocation &DataflowAnalyzer::computeMemoryLocation(const Term *term, const ReachingDefinitions &definitions) {
    return dataflow().setMemoryLocation(term, [&]() -> MemoryLocation {
        switch (term->kind()) {
            case Term::MEMORY_LOCATION_ACCESS: {
                return term->asMemoryLocationAccess()->memoryLocation();
            }
            case Term::DEREFERENCE: {
                auto dereference = term->asDereference();
                auto addressValue = computeValue(dereference->address(), definitions);

                if (addressValue->abstractValue().isConcrete()) {
                    BitAddr address;
                    if (dereference->domain() == MemoryDomain::MEMORY) {
                        if (!checkedByteAddressToBitAddress(
                                addressValue->abstractValue().asConcrete().value(),
                                dereference->size(), address))
                        {
                            return MemoryLocation();
                        }
                    } else {
                        if (!checkedBitAddress(
                                addressValue->abstractValue().asConcrete().value(),
                                dereference->size(), address))
                        {
                            return MemoryLocation();
                        }
                    }
                    return MemoryLocation(
                        dereference->domain(), address, dereference->size());
                } else if (addressValue->isStackOffset()) {
                    BitAddr address;
                    if (!checkedStackOffsetToBitAddress(
                            addressValue->stackOffset(), dereference->size(),
                            address))
                    {
                        return MemoryLocation();
                    }
                    return MemoryLocation(
                        MemoryDomain::STACK, address, dereference->size());
                } else {
                    return MemoryLocation();
                }
                break;
            }
            default: {
                log_.warning(tr("%1: Term kind %2 cannot have a memory location.").arg(Q_FUNC_INFO).arg(term->kind()));
                return MemoryLocation();
            }
        }
    }());
}

const ReachingDefinitions &DataflowAnalyzer::computeReachingDefinitions(const Term *term,
                                                                        const MemoryLocation &memoryLocation,
                                                                        const ReachingDefinitions &definitions) {
    auto &termDefinitions = dataflow().getDefinitions(term);

    if (isTracked(memoryLocation)) {
        definitions.project(memoryLocation, termDefinitions);
    } else {
        termDefinitions.clear();
    }

    return termDefinitions;
}

bool DataflowAnalyzer::isTracked(const MemoryLocation &memoryLocation) const {
    return memoryLocation && !architecture()->isGlobalMemory(memoryLocation);
}

Value *DataflowAnalyzer::computeValue(const Term *term, const MemoryLocation &memoryLocation,
                                      const ReachingDefinitions &definitions) {
    assert(term);
    assert(term->isRead());
    assert(memoryLocation || definitions.empty());

    auto value = dataflow().getValue(term);

    if (definitions.empty()) {
        /*
         * An earlier iteration may have observed a concrete reaching
         * definition before all CFG alternatives or effective addresses were
         * known.  A tracked read with no current definition denotes the
         * incoming value, not the last value computed for this syntax node.
         */
        if (isTracked(memoryLocation) ||
            dataflow().hasAmbiguousMemoryLocation(term))
        {
            value->setAbstractValue(AbstractValue(term->size(), -1, -1));
            value->makeAmbiguousStackOffset();
            value->makeNotProduct();
            value->makeNotReturnAddress();
        }
        return value;
    }

    auto byteOrder = architecture()->getByteOrder(memoryLocation.domain());

    /*
     * Merge abstract values.
     */
    AbstractValue abstractValue(value->abstractValue().size(), 0, 0);
    bool hasNonTermDefinition = false;
    ConstantValue coveredMask = 0;

    foreach (const auto &chunk, definitions.chunks()) {
        assert(memoryLocation.covers(chunk.location()));

        /*
         * Mask of bits inside abstractValue which are covered by chunk's location.
         */
        auto mask = bitMask<ConstantValue>(chunk.location().size());
        if (byteOrder == ByteOrder::LittleEndian) {
            mask = bitShift(mask, chunk.location().addr() - memoryLocation.addr());
        } else {
            mask = bitShift(mask, memoryLocation.endAddr() - chunk.location().endAddr());
        }
        coveredMask |= mask;

        if (chunk.hasUnknownDefinition() ||
            chunk.hasIncomingDefinition())
        {
            hasNonTermDefinition = true;
            abstractValue = AbstractValue(abstractValue.size(),
                abstractValue.zeroBits() | mask,
                abstractValue.oneBits() | mask,
                AbstractValue::exact);
        }

        foreach (auto definition, chunk.definitions()) {
            auto definitionLocation = dataflow().getMemoryLocation(definition);
            assert(definitionLocation.covers(chunk.location()));

            auto definitionValue = dataflow().getValue(definition);
            auto definitionAbstractValue = definitionValue->abstractValue();

            /*
             * Shift definition's abstract value to match term's location.
             */
            if (byteOrder == ByteOrder::LittleEndian) {
                definitionAbstractValue.shift(definitionLocation.addr() - memoryLocation.addr());
            } else {
                definitionAbstractValue.shift(memoryLocation.endAddr() - definitionLocation.endAddr());
            }

            /* Project the value to the defined location. */
            definitionAbstractValue.project(mask);

            /* Update the new abstract value. */
            abstractValue = AbstractValue(abstractValue.size(),
                abstractValue.zeroBits() | definitionAbstractValue.zeroBits(),
                abstractValue.oneBits() | definitionAbstractValue.oneBits());
        }
    }

    /* Bits which have no chunk on any alternative also retain their
     * function-entry value.  Treating the old lattice bottom as a value here
     * would let partially initialized aggregates participate in unsound
     * folding even though DefUseGraph correctly reports incomplete range
     * coverage. */
    const ConstantValue missingMask =
        bitMask<ConstantValue>(term->size()) & ~coveredMask;
    if (missingMask) {
        hasNonTermDefinition = true;
        abstractValue = AbstractValue(abstractValue.size(),
            abstractValue.zeroBits() | missingMask,
            abstractValue.oneBits() | missingMask,
            AbstractValue::exact);
    }

    value->setAbstractValue(abstractValue);

    /* Any unknown part prevents whole-value provenance classifications. */
    if (hasNonTermDefinition) {
        value->makeAmbiguousStackOffset();
        value->makeNotProduct();
        value->makeNotReturnAddress();
    }

    /*
     * Merge stack offset and product flags.
     *
     * Heuristic: merge information only from terms that define lower bits of the term's value.
     */
    const ReachingDefinitions::Chunk *lowerBitsChunk = nullptr;

    if (byteOrder == ByteOrder::LittleEndian) {
        if (definitions.chunks().front().location().addr() == memoryLocation.addr()) {
            lowerBitsChunk = &definitions.chunks().front();
        }
    } else {
        if (definitions.chunks().back().location().endAddr() == memoryLocation.endAddr()) {
            lowerBitsChunk = &definitions.chunks().back();
        }
    }

    if (lowerBitsChunk) {
        foreach (auto definition, lowerBitsChunk->definitions()) {
            auto definitionValue = dataflow().getValue(definition);

            if (definitionValue->isStackOffset()) {
                value->makeStackOffset(definitionValue->stackOffset());
            } else if (definitionValue->mayBeStackOffset()) {
                value->makeAmbiguousStackOffset();
            }
            if (definitionValue->isNotStackOffset()) {
                value->makeNotStackOffset();
            }

            if (definitionValue->isNotProduct()) {
                value->makeNotProduct();
            } else if (definitionValue->isProduct()) {
                value->makeProduct();
            }
        }
    }

    /*
     * Merge return address flag.
     */
    if (definitions.chunks().front().location() == memoryLocation) {
        foreach (auto definition, definitions.chunks().front().definitions()) {
            auto definitionValue = dataflow().getValue(definition);
            if (definitionValue->isNotReturnAddress()) {
                value->makeNotReturnAddress();
            } else if (definitionValue->isReturnAddress()) {
                value->makeReturnAddress();
            }
        }
    }

    return value;
}

Value *DataflowAnalyzer::computeValue(const UnaryOperator *unary, const ReachingDefinitions &definitions) {
    auto value = dataflow().getValue(unary);
    auto operandValue = computeValue(unary->operand(), definitions);

    value->setAbstractValue(apply(unary, operandValue->abstractValue()));

    switch (unary->operatorKind()) {
        case UnaryOperator::SIGN_EXTEND:
        case UnaryOperator::ZERO_EXTEND:
        case UnaryOperator::TRUNCATE:
            /* Resizing a symbolic frame address is not generally equivalent
             * to resizing its offset: the unknown frame base participates in
             * truncation and extension too. Preserve an exact offset only for
             * a representation-preserving no-op. */
            if (unary->size() == unary->operand()->size() &&
                operandValue->isStackOffset())
            {
                value->makeStackOffset(operandValue->stackOffset());
            } else if (operandValue->mayBeStackOffset()) {
                value->makeAmbiguousStackOffset();
            }
            if (operandValue->isNotStackOffset()) {
                value->makeNotStackOffset();
            }
            if (operandValue->isNotProduct()) {
                value->makeNotProduct();
            } else if (operandValue->isProduct()) {
                value->makeProduct();
            }
            break;
        default:
            if (operandValue->mayBeStackOffset()) {
                value->makeAmbiguousStackOffset();
            } else {
                value->makeNotStackOffset();
            }
            value->makeNotProduct();
            break;
    }

    value->makeNotReturnAddress();

    return value;
}

Value *DataflowAnalyzer::computeValue(const BinaryOperator *binary, const ReachingDefinitions &definitions) {
    auto value = dataflow().getValue(binary);
    auto leftValue = computeValue(binary->left(), definitions);
    auto rightValue = computeValue(binary->right(), definitions);

    value->setAbstractValue(apply(binary, leftValue->abstractValue(), rightValue->abstractValue()));

    /* Compute stack offset. */
    switch (binary->operatorKind()) {
        case BinaryOperator::ADD: {
            if (leftValue->isStackOffset()) {
                if (rightValue->abstractValue().isConcrete()) {
                    SignedConstantValue offset;
                    if (computeStackOffset(
                            leftValue->stackOffset(),
                            rightValue->abstractValue().asConcrete().value(),
                            binary->size(), false, offset))
                    {
                        value->makeStackOffset(offset);
                    } else {
                        value->makeAmbiguousStackOffset();
                    }
                } else if (rightValue->abstractValue().isNondeterministic()) {
                    value->makeNotStackOffset();
                }
            }
            if (rightValue->isStackOffset()) {
                if (leftValue->abstractValue().isConcrete()) {
                    SignedConstantValue offset;
                    if (computeStackOffset(
                            rightValue->stackOffset(),
                            leftValue->abstractValue().asConcrete().value(),
                            binary->size(), false, offset))
                    {
                        value->makeStackOffset(offset);
                    } else {
                        value->makeAmbiguousStackOffset();
                    }
                } else if (leftValue->abstractValue().isNondeterministic()) {
                    value->makeNotStackOffset();
                }
            }
            if (leftValue->isNotStackOffset() && rightValue->isNotStackOffset()) {
                value->makeNotStackOffset();
            }
            if ((leftValue->mayBeStackOffset() ||
                 rightValue->mayBeStackOffset()) &&
                !value->isStackOffset())
            {
                value->makeAmbiguousStackOffset();
            }
            break;
        }
        case BinaryOperator::SUB: {
            if (leftValue->isStackOffset() && rightValue->abstractValue().isConcrete()) {
                SignedConstantValue offset;
                if (computeStackOffset(
                        leftValue->stackOffset(),
                        rightValue->abstractValue().asConcrete().value(),
                        binary->size(), true, offset))
                {
                    value->makeStackOffset(offset);
                } else {
                    value->makeAmbiguousStackOffset();
                }
            } else if (leftValue->isNotStackOffset() || rightValue->abstractValue().isNondeterministic()) {
                value->makeNotStackOffset();
            }
            if ((leftValue->mayBeStackOffset() ||
                 rightValue->mayBeStackOffset()) &&
                !value->isStackOffset()) {
                value->makeAmbiguousStackOffset();
            }
            break;
        }
        case BinaryOperator::AND: {
            /* (frameBase + offset) & mask cannot be represented as a fixed
             * offset unless the frame base's congruence is known. This lattice
             * has no such alignment fact, so retain only possible provenance. */
            if ((leftValue->abstractValue().isNondeterministic() && leftValue->isNotStackOffset()) ||
                (rightValue->abstractValue().isNondeterministic() && rightValue->isNotStackOffset()))
            {
                value->makeNotStackOffset();
            }
            if ((leftValue->mayBeStackOffset() ||
                 rightValue->mayBeStackOffset()) &&
                !value->isStackOffset())
            {
                value->makeAmbiguousStackOffset();
            }
            break;
        }
        default: {
            if (leftValue->mayBeStackOffset() ||
                rightValue->mayBeStackOffset())
            {
                value->makeAmbiguousStackOffset();
            } else {
                value->makeNotStackOffset();
            }
            break;
        }
    }

    /* Compute product flag. */
    switch (binary->operatorKind()) {
        case BinaryOperator::MUL:
        case BinaryOperator::SHL:
            value->makeProduct();
            break;
        default:
            value->makeNotProduct();
            break;
    }

    value->makeNotReturnAddress();

    return value;
}

AbstractValue DataflowAnalyzer::apply(const UnaryOperator *unary, const AbstractValue &a) {
    switch (unary->operatorKind()) {
        case UnaryOperator::NOT:
            return ~a;
        case UnaryOperator::NEGATION:
            return -a;
        case UnaryOperator::SIGN_EXTEND:
            return dflow::AbstractValue(a).signExtend(unary->size());
        case UnaryOperator::ZERO_EXTEND:
            return dflow::AbstractValue(a).zeroExtend(unary->size());
        case UnaryOperator::TRUNCATE:
            return dflow::AbstractValue(a).resize(unary->size());
        default:
            log_.warning(tr("%1: Unknown unary operator kind: %2.").arg(Q_FUNC_INFO).arg(unary->operatorKind()));
            return dflow::AbstractValue();
    }
}

AbstractValue DataflowAnalyzer::apply(const BinaryOperator *binary, const AbstractValue &a, const AbstractValue &b) {
    switch (binary->operatorKind()) {
        case BinaryOperator::AND:
            return a & b;
        case BinaryOperator::OR:
            return a | b;
        case BinaryOperator::XOR:
            return a ^ b;
        case BinaryOperator::SHL:
            return a << b;
        case BinaryOperator::SHR:
            return a.asUnsigned() >> b;
        case BinaryOperator::SAR:
            return a.asSigned() >> b;
        case BinaryOperator::ADD:
            return a + b;
        case BinaryOperator::SUB:
            return a - b;
        case BinaryOperator::MUL:
            return a * b;
        case BinaryOperator::SIGNED_DIV:
            return a.asSigned() / b;
        case BinaryOperator::SIGNED_REM:
            return a.asSigned() % b;
        case BinaryOperator::UNSIGNED_DIV:
            return a.asUnsigned() / b;
        case BinaryOperator::UNSIGNED_REM:
            return a.asUnsigned() % b;
        case BinaryOperator::EQUAL:
            return a == b;
        case BinaryOperator::SIGNED_LESS:
            return a.asSigned() < b;
        case BinaryOperator::SIGNED_LESS_OR_EQUAL:
            return a.asSigned() <= b;
        case BinaryOperator::UNSIGNED_LESS:
            return a.asUnsigned() < b;
        case BinaryOperator::UNSIGNED_LESS_OR_EQUAL:
            return a.asUnsigned() <= b;
        default:
            log_.warning(tr("%1: Unknown binary operator kind: %2.").arg(Q_FUNC_INFO).arg(binary->operatorKind()));
            return dflow::AbstractValue();
    }
}

void DataflowAnalyzer::handleWrite(const Term *term, const MemoryLocation &memoryLocation, ReachingDefinitions &definitions) {
    std::vector<MemoryLocation> possibleStackWrites;
    if (!memoryLocation) {
        const Dereference *dereference = term->asDereference();
        const Value *addressValue = dereference ?
            dataflow().findValue(dereference->address()) : nullptr;
        if (addressValue && addressValue->mayBeStackOffset()) {
            /* Snapshot ranges before removing an earlier dynamic occurrence
             * of this same write term at the dataflow fixpoint. */
            possibleStackWrites =
                definitions.getDefinedMemoryLocationsWithin(
                    MemoryDomain::STACK);
        }
    }

    definitions.filterOut(
        [term](const MemoryLocation &, const Term *definition) -> bool {
            return definition == term;
        }
    );

    if (isTracked(memoryLocation)) {
        definitions.addDefinition(memoryLocation, term);
    } else if (!possibleStackWrites.empty()) {
        /* An unresolved indirect write is a may-write, not a no-op.  If its
         * address may be derived from the current frame, conservatively add
         * an unknown alternative to every tracked stack interval.  Definite
         * non-stack addresses leave frame state untouched. */
        addPossibleUnknownDefinitions(possibleStackWrites, definitions);
    }
}

void DataflowAnalyzer::handleKill(const MemoryLocation &memoryLocation, ReachingDefinitions &definitions) {
    if (isTracked(memoryLocation)) {
        definitions.killDefinitions(memoryLocation);
    }
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
