/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "CallFrameAnalyzer.h"

#include <algorithm>
#include <climits>
#include <cstddef>
#include <limits>
#include <map>
#include <set>
#include <vector>

#include <nc/common/Foreach.h>

#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Term.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/ReachingDefinitions.h>
#include <nc/core/ir/dflow/Value.h>

#include "CallHook.h"
#include "Convention.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

bool getStackOffset(const Term *term, const dflow::Dataflow &dataflow,
                    SignedConstantValue &result) {
    const dflow::Value *value = term ? dataflow.findValue(term) : nullptr;
    if (!value || !value->isStackOffset()) {
        return false;
    }
    result = value->stackOffset();
    return true;
}

bool checkedAdd(SignedConstantValue left, ByteSize right,
                SignedConstantValue &result) {
    if (right < 0 ||
        left > (std::numeric_limits<SignedConstantValue>::max)() - right)
    {
        return false;
    }
    result = left + right;
    return true;
}

bool checkedPositiveDifference(SignedConstantValue high,
                               SignedConstantValue low,
                               ByteSize &result) {
    if (high <= low ||
        (low < 0 &&
         high > (std::numeric_limits<SignedConstantValue>::max)() + low))
    {
        return false;
    }
    result = high - low;
    return true;
}

bool checkedByteOffsetToBitAddress(SignedConstantValue offset,
                                   BitAddr &result) {
    if (offset < (std::numeric_limits<BitAddr>::min)() / CHAR_BIT ||
        offset > (std::numeric_limits<BitAddr>::max)() / CHAR_BIT)
    {
        return false;
    }
    result = offset * CHAR_BIT;
    return true;
}

void collectStackPointerReads(const Term *term,
                              const MemoryLocation &stackPointer,
                              const dflow::Dataflow &dataflow,
                              std::vector<const Term *> &result) {
    assert(term != nullptr);
    if (term->isRead() &&
        dataflow.getMemoryLocation(term) == stackPointer)
    {
        result.push_back(term);
    }
    term->callOnChildren(
        [&](const Term *child) {
            collectStackPointerReads(
                child, stackPointer, dataflow, result);
        });
}

/**
 * Recognizes a semantic SP-relative update.  Looking at the stabilized value
 * of both the input SP term and the result accepts equivalent instruction
 * encodings (ADD, LEA, or lifted custom instructions) without matching an
 * opcode or a particular expression tree.
 */
bool getRelativeStackUpdate(const Assignment *assignment,
                            const MemoryLocation &stackPointer,
                            const dflow::Dataflow &dataflow,
                            SignedConstantValue &oldOffset,
                            SignedConstantValue &newOffset) {
    if (!assignment ||
        dataflow.getMemoryLocation(assignment->left()) != stackPointer ||
        !getStackOffset(assignment->right(), dataflow, newOffset))
    {
        return false;
    }

    std::vector<const Term *> stackPointerReads;
    collectStackPointerReads(
        assignment->right(), stackPointer, dataflow, stackPointerReads);
    if (stackPointerReads.size() != 1 ||
        !getStackOffset(stackPointerReads.front(), dataflow, oldOffset))
    {
        return false;
    }
    return true;
}

const Term *getUniqueDefinition(
        const dflow::ReachingDefinitions &definitions,
        const MemoryLocation &slot) {
    const dflow::ReachingDefinitions projected =
        definitions.projected(slot);
    BitAddr coveredUntil = slot.addr();
    const Term *result = nullptr;

    foreach (const dflow::ReachingDefinitions::Chunk &chunk,
             projected.chunks()) {
        if (chunk.location().addr() != coveredUntil ||
            chunk.hasIncomingDefinition() ||
            chunk.hasUnknownDefinition() ||
            chunk.definitions().size() != 1)
        {
            return nullptr;
        }
        if (result && result != chunk.definitions().front()) {
            return nullptr;
        }
        result = chunk.definitions().front();
        coveredUntil = chunk.location().endAddr();
    }

    return result && coveredUntil == slot.endAddr() ? result : nullptr;
}

struct PushEvidence {
    const arch::Instruction *instruction;
    const Statement *stackPointerAssignment;
    std::size_t firstStatementIndex;

    PushEvidence(): instruction(nullptr), stackPointerAssignment(nullptr),
                    firstStatementIndex(0) {}
};

bool getPushEvidence(
        const Term *definition, const MemoryLocation &slot,
        ByteSize slotSize, const MemoryLocation &stackPointer,
        const dflow::Dataflow &dataflow,
        const std::vector<const Statement *> &statements,
        const std::map<const Statement *, std::size_t> &statementIndices,
        PushEvidence &result) {
    if (!definition || !definition->isWrite() ||
        dataflow.getMemoryLocation(definition) != slot)
    {
        return false;
    }

    const Statement *definitionStatement = definition->statement();
    const Assignment *definitionAssignment =
        definitionStatement ? definitionStatement->asAssignment() : nullptr;
    if (!definitionAssignment ||
        definitionAssignment->left() != definition ||
        !definitionStatement->instruction())
    {
        return false;
    }

    const auto definitionIndex = statementIndices.find(definitionStatement);
    if (definitionIndex == statementIndices.end()) {
        return false;
    }

    const arch::Instruction *instruction =
        definitionStatement->instruction();
    const Statement *stackPointerAssignment = nullptr;
    std::size_t stackPointerAssignmentIndex = 0;
    std::size_t firstStatementIndex = definitionIndex->second;

    for (std::size_t index = 0; index < statements.size(); ++index) {
        const Statement *statement = statements[index];
        if (statement->instruction() != instruction) {
            continue;
        }
        firstStatementIndex = std::min(firstStatementIndex, index);
        const Assignment *assignment = statement->asAssignment();
        if (!assignment ||
            dataflow.getMemoryLocation(assignment->left()) != stackPointer)
        {
            continue;
        }
        if (stackPointerAssignment) {
            return false;
        }

        SignedConstantValue oldOffset;
        SignedConstantValue newOffset;
        ByteSize decrement;
        if (!getRelativeStackUpdate(
                assignment, stackPointer, dataflow,
                oldOffset, newOffset) ||
            !checkedPositiveDifference(oldOffset, newOffset, decrement) ||
            decrement != slotSize ||
            newOffset != slot.addr() / CHAR_BIT)
        {
            return false;
        }
        stackPointerAssignment = statement;
        stackPointerAssignmentIndex = index;
    }

    if (!stackPointerAssignment ||
        stackPointerAssignmentIndex >= definitionIndex->second)
    {
        return false;
    }

    result.instruction = instruction;
    result.stackPointerAssignment = stackPointerAssignment;
    result.firstStatementIndex = firstStatementIndex;
    return true;
}

} // anonymous namespace

boost::optional<ByteSize>
CallFrameAnalyzer::inferCallerCleanupArgumentSize(
        const Call *call, const Convention *convention,
        const CallHook *hook, const dflow::Dataflow &dataflow) {
    if (!call || !convention || !hook || !dataflow.converged() ||
        !call->basicBlock() || !call->instruction() ||
        !hook->snapshotStatement() || !hook->stackPointer() ||
        !convention->stackPointer() || convention->calleeCleanup() ||
        !convention->argumentGroups().empty())
    {
        return boost::none;
    }

    const MemoryLocation &stackPointer = convention->stackPointer();
    const BitSize firstArgumentOffset = convention->firstArgumentOffset();
    const BitSize argumentAlignment = convention->argumentAlignment();
    if (firstArgumentOffset != stackPointer.size() ||
        argumentAlignment != stackPointer.size() ||
        firstArgumentOffset <= 0 ||
        firstArgumentOffset % CHAR_BIT != 0)
    {
        return boost::none;
    }
    const ByteSize slotSize = argumentAlignment / CHAR_BIT;
    const ByteSize returnAddressSize = firstArgumentOffset / CHAR_BIT;

    SignedConstantValue callStackOffset;
    SignedConstantValue argumentsStartOffset;
    if (!getStackOffset(
            hook->stackPointer(), dataflow, callStackOffset) ||
        !checkedAdd(
            callStackOffset, returnAddressSize,
            argumentsStartOffset))
    {
        return boost::none;
    }

    std::vector<const Statement *> statements;
    std::map<const Statement *, std::size_t> statementIndices;
    std::size_t callIndex = (std::numeric_limits<std::size_t>::max)();
    foreach (const Statement *statement,
             call->basicBlock()->statements()) {
        if (statement == call) {
            callIndex = statements.size();
        }
        statementIndices[statement] = statements.size();
        statements.push_back(statement);
    }
    if (callIndex == (std::numeric_limits<std::size_t>::max)()) {
        return boost::none;
    }

    /* The cleanup must be the first machine instruction after the call.  In
     * particular, do not scan forward to an epilogue and reinterpret a local
     * frame teardown as argument cleanup. */
    const arch::Instruction *cleanupInstruction = nullptr;
    for (std::size_t index = callIndex + 1;
         index < statements.size(); ++index)
    {
        const arch::Instruction *instruction =
            statements[index]->instruction();
        if (instruction && instruction != call->instruction()) {
            cleanupInstruction = instruction;
            break;
        }
    }
    if (!cleanupInstruction) {
        return boost::none;
    }

    const Assignment *cleanupAssignment = nullptr;
    SignedConstantValue cleanupOldOffset = 0;
    SignedConstantValue cleanupNewOffset = 0;
    for (std::size_t index = callIndex + 1;
         index < statements.size(); ++index)
    {
        const Statement *statement = statements[index];
        if (statement->instruction() != cleanupInstruction) {
            continue;
        }
        if (statement->is<Call>() || statement->is<Jump>() ||
            statement->is<Halt>() || statement->is<InlineAssembly>())
        {
            return boost::none;
        }
        const Assignment *assignment = statement->asAssignment();
        if (!assignment ||
            dataflow.getMemoryLocation(assignment->left()) != stackPointer)
        {
            continue;
        }
        if (cleanupAssignment ||
            !getRelativeStackUpdate(
                assignment, stackPointer, dataflow,
                cleanupOldOffset, cleanupNewOffset))
        {
            return boost::none;
        }
        cleanupAssignment = assignment;
    }

    ByteSize argumentSize;
    if (!cleanupAssignment ||
        cleanupOldOffset != argumentsStartOffset ||
        !checkedPositiveDifference(
            cleanupNewOffset, cleanupOldOffset, argumentSize) ||
        argumentSize % slotSize != 0)
    {
        return boost::none;
    }

    const ConstantValue slotCount =
        static_cast<ConstantValue>(argumentSize / slotSize);
    if (slotCount == 0 ||
        slotCount > (std::numeric_limits<std::size_t>::max)() ||
        slotCount > static_cast<ConstantValue>(callIndex))
    {
        return boost::none;
    }

    BitAddr argumentsStartAddress;
    BitAddr argumentsEndAddress;
    if (!checkedByteOffsetToBitAddress(
            argumentsStartOffset, argumentsStartAddress) ||
        !checkedByteOffsetToBitAddress(
            cleanupNewOffset, argumentsEndAddress) ||
        argumentsEndAddress <= argumentsStartAddress)
    {
        return boost::none;
    }

    const dflow::ReachingDefinitions &definitions =
        dataflow.getDefinitions(hook->snapshotStatement());
    std::set<const arch::Instruction *> pushInstructions;
    std::set<const Statement *> pushStackPointerAssignments;
    std::size_t setupStartIndex = callIndex;

    BitAddr slotAddress = argumentsStartAddress;
    for (std::size_t index = 0;
         index < static_cast<std::size_t>(slotCount); ++index)
    {
        if (slotAddress >
            (std::numeric_limits<BitAddr>::max)() - argumentAlignment)
        {
            return boost::none;
        }
        const BitAddr slotEndAddress = slotAddress + argumentAlignment;
        if (slotEndAddress > argumentsEndAddress) {
            return boost::none;
        }
        const MemoryLocation slot(
            MemoryDomain::STACK, slotAddress, argumentAlignment);
        const Term *definition = getUniqueDefinition(definitions, slot);

        PushEvidence evidence;
        if (!getPushEvidence(
                definition, slot, slotSize, stackPointer, dataflow,
                statements, statementIndices, evidence) ||
            statementIndices.at(definition->statement()) >= callIndex)
        {
            return boost::none;
        }
        if (!pushInstructions.insert(evidence.instruction).second) {
            /* One stack-decrement instruction cannot establish two distinct
             * ABI slots in the restricted call-frame model. */
            return boost::none;
        }
        pushStackPointerAssignments.insert(
            evidence.stackPointerAssignment);
        setupStartIndex = std::min(
            setupStartIndex, evidence.firstStatementIndex);
        slotAddress = slotEndAddress;
    }

    if (slotAddress != argumentsEndAddress ||
        pushInstructions.size() != static_cast<std::size_t>(slotCount))
    {
        return boost::none;
    }

    /* No hidden stack motion or nested call may occur between the first
     * outgoing-slot push and this call.  Stack-neutral computations are
     * permitted, so argument expressions need not be adjacent opcodes. */
    for (std::size_t index = setupStartIndex;
         index < callIndex; ++index)
    {
        const Statement *statement = statements[index];
        if (statement->is<Call>() || statement->is<Jump>() ||
            statement->is<Halt>() || statement->is<InlineAssembly>())
        {
            return boost::none;
        }
        const Assignment *assignment = statement->asAssignment();
        if (assignment &&
            dataflow.getMemoryLocation(assignment->left()) == stackPointer &&
            pushStackPointerAssignments.find(statement) ==
                pushStackPointerAssignments.end() &&
            statement->instruction() != call->instruction())
        {
            return boost::none;
        }
    }

    return argumentSize;
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
