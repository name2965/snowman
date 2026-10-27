/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <memory>
#include <stdexcept>

#include <nc/common/CancellationToken.h>
#include <nc/common/SizedValue.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/cflow/Graph.h>
#include <nc/core/ir/dflow/AbstractValue.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/ReachingDefinitions.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/idiom/IdiomAnalyzer.h>
#include <nc/core/ir/idiom/Idioms.h>
#include <nc/core/ir/idiom/MemoryFill.h>
#include <nc/core/ir/idiom/MemoryFillLoweringPolicy.h>
#include <nc/core/ir/liveness/Liveness.h>

using namespace nc;
using namespace nc::core;
using namespace nc::core::ir;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

std::unique_ptr<Term> constant(SmallBitSize size, ConstantValue value) {
    return std::unique_ptr<Term>(new Constant(SizedValue(size, value)));
}

BasicBlock *addBlock(Function &function) {
    std::unique_ptr<BasicBlock> block(new BasicBlock());
    BasicBlock *result = block.get();
    function.addBasicBlock(std::move(block));
    return result;
}

Term *addConstantDefinition(BasicBlock *block,
                            const MemoryLocation &location,
                            ConstantValue value) {
    std::unique_ptr<Term> left(new MemoryLocationAccess(location));
    Term *definition = left.get();
    block->pushBack(std::unique_ptr<Statement>(new Assignment(
        std::move(left), constant(location.size<SmallBitSize>(), value))));
    return definition;
}

void setLoopDefinitions(dflow::Dataflow &dataflow, const Term *read,
                        const MemoryLocation &location,
                        const Term *entryDefinition,
                        const Term *loopDefinition) {
    dflow::ReachingDefinitions definitions;
    definitions.addDefinition(location, entryDefinition);
    dflow::ReachingDefinitions backEdgeDefinitions;
    backEdgeDefinitions.addDefinition(location, loopDefinition);
    definitions.merge(backEdgeDefinitions);
    dataflow.getDefinitions(read) = definitions;
}

enum BarrierKind {
    NO_BARRIER,
    CALL_BARRIER,
    INLINE_ASSEMBLY_BARRIER
};

/**
 * A byte-fill inner loop which is re-entered by an outer loop.  This shape
 * catches the distinction between a merely dominating initializer and the
 * dedicated inner-loop preheader which executes on every dynamic entry.
 */
class MemoryFillFixture {
    Function function_;
    dflow::Dataflow dataflow_;
    cflow::Graph graph_;
    liveness::Liveness liveness_;
    idiom::FunctionIdioms idioms_;
    BasicBlock *innerHeader_;

public:
    MemoryFillFixture(bool initializeInInnerPreheader, BarrierKind barrier,
                      ConstantValue initialCount = 4):
        innerHeader_(nullptr)
    {
        const MemoryLocation destination(
            MemoryDomain::FIRST_REGISTER + 50, 0, 32);
        const MemoryLocation count(
            MemoryDomain::FIRST_REGISTER + 51, 0, 32);

        BasicBlock *entry = addBlock(function_);
        BasicBlock *outerHeader = addBlock(function_);
        BasicBlock *innerPreheader = addBlock(function_);
        innerHeader_ = addBlock(function_);
        BasicBlock *innerBody = addBlock(function_);
        BasicBlock *innerExit = addBlock(function_);
        BasicBlock *outerLatch = addBlock(function_);
        BasicBlock *functionExit = addBlock(function_);
        function_.setEntry(entry);

        BasicBlock *initializer = initializeInInnerPreheader ?
            innerPreheader : entry;
        Term *initialDestination = addConstantDefinition(
            initializer, destination, 0x1000);
        Term *initialElementCount = addConstantDefinition(
            initializer, count, initialCount);

        entry->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(outerHeader))));
        outerHeader->pushBack(std::unique_ptr<Statement>(new Jump(
            constant(1, 1), JumpTarget(innerPreheader),
            JumpTarget(functionExit))));

        if (barrier == CALL_BARRIER) {
            innerPreheader->pushBack(std::unique_ptr<Statement>(
                new Call(constant(32, 0x2000))));
        } else if (barrier == INLINE_ASSEMBLY_BARRIER) {
            innerPreheader->pushBack(
                std::unique_ptr<Statement>(new InlineAssembly()));
        }
        innerPreheader->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(innerHeader_))));

        std::unique_ptr<Term> headerCountStorage(
            new MemoryLocationAccess(count));
        Term *headerCount = headerCountStorage.get();
        innerHeader_->pushBack(std::unique_ptr<Statement>(new Jump(
            std::move(headerCountStorage), JumpTarget(innerBody),
            JumpTarget(innerExit))));

        std::unique_ptr<Term> storeAddressStorage(
            new MemoryLocationAccess(destination));
        Term *storeAddress = storeAddressStorage.get();
        Statement *memoryWrite = innerBody->pushBack(
            std::unique_ptr<Statement>(new Assignment(
                std::unique_ptr<Term>(new Dereference(
                    std::move(storeAddressStorage), MemoryDomain::MEMORY, 8)),
                constant(8, 0x5a))));

        std::unique_ptr<Term> destinationUpdateLeftStorage(
            new MemoryLocationAccess(destination));
        Term *destinationUpdate = destinationUpdateLeftStorage.get();
        std::unique_ptr<Term> destinationReadStorage(
            new MemoryLocationAccess(destination));
        Term *destinationRead = destinationReadStorage.get();
        std::unique_ptr<Term> destinationStepStorage = constant(32, 1);
        Term *destinationStep = destinationStepStorage.get();
        innerBody->pushBack(std::unique_ptr<Statement>(new Assignment(
            std::move(destinationUpdateLeftStorage),
            std::unique_ptr<Term>(new BinaryOperator(
                BinaryOperator::ADD, std::move(destinationReadStorage),
                std::move(destinationStepStorage), 32)))));

        std::unique_ptr<Term> countUpdateLeftStorage(
            new MemoryLocationAccess(count));
        Term *countUpdate = countUpdateLeftStorage.get();
        std::unique_ptr<Term> countReadStorage(
            new MemoryLocationAccess(count));
        Term *countRead = countReadStorage.get();
        std::unique_ptr<Term> countStepStorage = constant(32, 1);
        Term *countStep = countStepStorage.get();
        innerBody->pushBack(std::unique_ptr<Statement>(new Assignment(
            std::move(countUpdateLeftStorage),
            std::unique_ptr<Term>(new BinaryOperator(
                BinaryOperator::SUB, std::move(countReadStorage),
                std::move(countStepStorage), 32)))));
        innerBody->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(innerHeader_))));

        innerExit->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(outerLatch))));
        outerLatch->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(outerHeader))));
        functionExit->pushBack(std::unique_ptr<Statement>(new Halt()));

        dataflow_.setMemoryLocation(initialDestination, destination);
        dataflow_.setMemoryLocation(initialElementCount, count);
        dataflow_.setMemoryLocation(headerCount, count);
        dataflow_.setMemoryLocation(storeAddress, destination);
        dataflow_.setMemoryLocation(destinationUpdate, destination);
        dataflow_.setMemoryLocation(destinationRead, destination);
        dataflow_.setMemoryLocation(countUpdate, count);
        dataflow_.setMemoryLocation(countRead, count);

        dataflow_.getValue(destinationStep)->setAbstractValue(
            dflow::AbstractValue(SizedValue(32, 1)));
        dataflow_.getValue(countStep)->setAbstractValue(
            dflow::AbstractValue(SizedValue(32, 1)));

        setLoopDefinitions(dataflow_, headerCount, count,
                           initialElementCount, countUpdate);
        setLoopDefinitions(dataflow_, countRead, count,
                           initialElementCount, countUpdate);
        setLoopDefinitions(dataflow_, storeAddress, destination,
                           initialDestination, destinationUpdate);
        setLoopDefinitions(dataflow_, destinationRead, destination,
                           initialDestination, destinationUpdate);
        dataflow_.setConverged(true);

        const CancellationToken canceled;
        idiom::IdiomAnalyzer(
            idioms_, &function_, graph_, dataflow_, liveness_, canceled)
            .analyze();

        check(memoryWrite->asAssignment() != nullptr,
              "the fixture's memory operation must remain an assignment");
    }

    const idiom::MemoryFill *memoryFill() const {
        return idioms_.getMemoryFill(innerHeader_);
    }
};

void testMemoryFillRecognitionGuards() {
    check(MemoryFillFixture(true, NO_BARRIER).memoryFill() != nullptr,
          "a canonical re-entered byte-fill loop must be recognized");

    check(MemoryFillFixture(false, NO_BARRIER).memoryFill() == nullptr,
          "an initializer outside the dynamic inner-loop preheader must be rejected");

    check(MemoryFillFixture(true, CALL_BARRIER).memoryFill() == nullptr,
          "an opaque call between capture and recurrence must block recognition");

    check(MemoryFillFixture(true, INLINE_ASSEMBLY_BARRIER).memoryFill() ==
              nullptr,
          "inline assembly with unknown effects must block recognition");

    check(MemoryFillFixture(true, NO_BARRIER, 0).memoryFill() != nullptr,
          "zero-trip fills may be described but must be filtered at lowering");
}

idiom::MemoryFillLoweringFacts safeLoweringFacts() {
    idiom::MemoryFillLoweringFacts facts;
    facts.dataflowConverged = true;
    facts.pointerSize = 32;
    facts.addressSize = 32;
    facts.destinationSize = 32;
    facts.elementSize = 8;
    facts.stride = 1;
    facts.fillIsConcrete = true;
    facts.fill = 0x5a;
    facts.countIsConcrete = true;
    facts.count = 4;
    facts.destinationIsConcrete = true;
    facts.destinationMayBeStackOffset = false;
    facts.destination = 0x1040;
    facts.hasContainingSection = true;
    facts.sectionAddress = 0x1000;
    facts.sectionSize = 0x100;
    facts.sectionIsAllocated = true;
    facts.sectionIsWritable = true;
    facts.sectionIsExecutable = false;
    return facts;
}

void testMemoryFillLoweringPolicy() {
    idiom::MemoryFillLoweringFacts facts = safeLoweringFacts();
    check(idiom::isMemoryFillLoweringSafe(facts),
          "a bounded non-wrapping byte fill must be lowerable");

    facts = safeLoweringFacts();
    facts.fillIsConcrete = false;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "a captured dynamic fill value must not be re-evaluated later");

    facts = safeLoweringFacts();
    facts.count = 0;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "a zero-trip loop must not gain a library-call evaluation");

    facts = safeLoweringFacts();
    facts.countIsConcrete = false;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "a dynamic count needs a range proof before lowering");

    facts = safeLoweringFacts();
    facts.addressSize = 64;
    facts.destinationSize = 64;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "the induction width must equal the target pointer width");

    facts = safeLoweringFacts();
    facts.destination = 0xffffffffU;
    facts.count = 2;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "the final byte address must not wrap at pointer width");

    facts = safeLoweringFacts();
    facts.destination = 0x10ff;
    facts.count = 1;
    check(idiom::isMemoryFillLoweringSafe(facts),
          "writing the final byte of an object must remain valid");
    facts.count = 2;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "a fill crossing its containing section must be rejected");

    facts = safeLoweringFacts();
    facts.sectionIsExecutable = true;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "writable-executable memory must retain explicit stores");

    facts = safeLoweringFacts();
    facts.elementSize = 32;
    facts.stride = 4;
    facts.destination = 0x1040;
    check(!idiom::isMemoryFillLoweringSafe(facts),
          "wide stores need an alignment and ordinary-memory proof");
}

} // anonymous namespace

int main() {
    try {
        testMemoryFillRecognitionGuards();
        testMemoryFillLoweringPolicy();
    } catch (const std::exception &exception) {
        std::cerr << "memory-fill regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
