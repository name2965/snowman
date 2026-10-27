/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <climits>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include <nc/common/BitTwiddling.h>
#include <nc/common/CancellationToken.h>
#include <nc/common/CheckedAddress.h>
#include <nc/common/Foreach.h>
#include <nc/common/LogToken.h>
#include <nc/common/SizedValue.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/image/ByteSource.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/FunctionsGenerator.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/PostDominators.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallSignature.h>
#include <nc/core/ir/calling/CallFrameAnalyzer.h>
#include <nc/core/ir/calling/CallHook.h>
#include <nc/core/ir/calling/CalleeId.h>
#include <nc/core/ir/calling/Convention.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/EntryHook.h>
#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/ReturnHook.h>
#include <nc/core/ir/calling/SignatureAnalyzer.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cgen/Utils.h>
#include <nc/core/ir/dflow/AbstractValue.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DataflowAnalyzer.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/dflow/DefUseGraph.h>
#include <nc/core/ir/dflow/ExpressionIdentity.h>
#include <nc/core/ir/dflow/ReachingDefinitions.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/dflow/ValueProvenance.h>
#include <nc/core/ir/liveness/Liveness.h>
#include <nc/core/ir/liveness/LivenessAnalyzer.h>
#include <nc/core/ir/liveness/Livenesses.h>
#include <nc/core/irgen/InstructionAnalyzer.h>

using namespace nc;
using namespace nc::core;
using namespace nc::core::ir;
using namespace nc::core::ir::dflow;

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

Term *addDefinition(BasicBlock *block, const MemoryLocation &location,
                    std::unique_ptr<Term> source,
                    Term **sourceTerm = nullptr) {
    check(block != nullptr, "definition block must exist");
    check(source.get() != nullptr, "definition source must exist");

    if (sourceTerm) {
        *sourceTerm = source.get();
    }
    std::unique_ptr<Term> destination(new MemoryLocationAccess(location));
    Term *definition = destination.get();
    block->pushBack(std::unique_ptr<Statement>(
        new Assignment(std::move(destination), std::move(source))));
    return definition;
}

struct ReadDefinition {
    Term *read;
    Term *definition;
    Term *expression;
};

ReadDefinition addReadDefinition(BasicBlock *block,
                                 const MemoryLocation &readLocation,
                                 const MemoryLocation &writeLocation) {
    std::unique_ptr<Term> read(new MemoryLocationAccess(readLocation));
    Term *readTerm = read.get();
    Term *writeTerm = addDefinition(
        block, writeLocation, std::move(read));
    return ReadDefinition{readTerm, writeTerm, readTerm};
}

const ReachingDefinitions::Chunk *findChunk(
        const ReachingDefinitions &definitions,
        const MemoryLocation &location) {
    foreach (const auto &chunk, definitions.chunks()) {
        if (chunk.location() == location) {
            return &chunk;
        }
    }
    return nullptr;
}

/** Minimal architecture needed by the architecture-neutral dataflow tests. */
class TestArchitecture: public arch::Architecture {
public:
    std::unique_ptr<arch::Disassembler> createDisassembler() const override {
        return std::unique_ptr<arch::Disassembler>();
    }

    std::unique_ptr<irgen::InstructionAnalyzer>
    createInstructionAnalyzer() const override {
        return std::unique_ptr<irgen::InstructionAnalyzer>();
    }

    ByteOrder getByteOrder(Domain) const override {
        return ByteOrder::LittleEndian;
    }
};

class TestInstruction: public arch::Instruction {
public:
    TestInstruction(ByteAddr address, SmallByteSize size):
        arch::Instruction(address, size)
    {}

    void print(QTextStream &) const override {}
};

class TestDisassemblyArchitecture: public TestArchitecture {
public:
    TestDisassemblyArchitecture() {
        setBitness(64);
        setMaxInstructionSize(4);
    }
};

class TopAddressByteSource: public image::ByteSource {
    ByteAddr begin_;
    ByteAddr end_;
    bool overreport_;

public:
    TopAddressByteSource(ByteAddr begin, ByteAddr end,
                         bool overreport = false):
        begin_(begin), end_(end), overreport_(overreport)
    {}

    ByteSize readBytes(ByteAddr address, void *buffer,
                       ByteSize size) const override {
        if (address < begin_ || address >= end_ || size <= 0) {
            return 0;
        }

        const ByteSize remaining = end_ - address;
        const ByteSize count = size < remaining ? size : remaining;
        char *bytes = static_cast<char *>(buffer);
        for (ByteSize i = 0; i < count; ++i) {
            bytes[i] = static_cast<char>(0x90);
        }
        return overreport_ ? size + 1 : count;
    }
};

class TestDisassembler: public arch::Disassembler {
    SmallByteSize decodedSize_;
    std::vector<ByteAddr> attemptedAddresses_;

public:
    TestDisassembler(const arch::Architecture *architecture,
                     SmallByteSize decodedSize):
        arch::Disassembler(architecture), decodedSize_(decodedSize)
    {}

    std::shared_ptr<arch::Instruction> disassembleSingleInstruction(
            ByteAddr address, const void *, ByteSize size) override {
        attemptedAddresses_.push_back(address);
        if (size <= 0) {
            return std::shared_ptr<arch::Instruction>();
        }
        return std::shared_ptr<arch::Instruction>(
            new TestInstruction(address, decodedSize_));
    }

    const std::vector<ByteAddr> &attemptedAddresses() const {
        return attemptedAddresses_;
    }
};

class TestConvention: public calling::Convention {
public:
    MemoryLocation volatileLocation;
    MemoryLocation returnLocation;

    TestConvention():
        calling::Convention(QLatin1String("test")),
        volatileLocation(MemoryDomain::FIRST_REGISTER + 40, 0, 32),
        returnLocation(MemoryDomain::FIRST_REGISTER + 41, 0, 32)
    {
        setStackPointer(MemoryLocation(
            MemoryDomain::FIRST_REGISTER + 42, 0, 32));
        addClobberedLocations(
            std::vector<MemoryLocation>(1, volatileLocation));
        addReturnValueLocation(returnLocation);
    }
};

class TestStackConvention: public calling::Convention {
public:
    MemoryLocation stackPointerLocation;

    explicit TestStackConvention(bool calleeCleanup = false):
        calling::Convention(QLatin1String("test-stack")),
        stackPointerLocation(
            MemoryDomain::FIRST_REGISTER + 44, 0, 32)
    {
        setStackPointer(stackPointerLocation);
        setFirstArgumentOffset(32);
        setArgumentAlignment(32);
        setCalleeCleanup(calleeCleanup);
    }
};

class TestRegisterInferenceConvention: public calling::Convention {
public:
    MemoryLocation argumentLocation;
    MemoryLocation returnLocation;

    TestRegisterInferenceConvention():
        calling::Convention(QLatin1String("test-register-inference")),
        argumentLocation(MemoryDomain::FIRST_REGISTER + 46, 0, 32),
        returnLocation(MemoryDomain::FIRST_REGISTER + 47, 0, 32)
    {
        addArgumentGroup(
            std::vector<MemoryLocation>(1, argumentLocation));
        addReturnValueLocation(returnLocation);
    }
};

void testLateFunctionEntryPreservesFallthrough() {
    Program program;
    TestInstruction firstInstruction(0x1000, 1);
    TestInstruction entryInstruction(0x1001, 1);

    BasicBlock *block = program.getBasicBlockForInstruction(
        &firstInstruction);
    std::unique_ptr<Statement> firstStatement(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            MemoryLocation(MemoryDomain::FIRST_REGISTER + 50, 0, 32))),
        constant(32, 1)));
    firstStatement->setInstruction(&firstInstruction);
    block->pushBack(std::move(firstStatement));

    check(program.getBasicBlockForInstruction(&entryInstruction) == block,
          "fixture instructions must initially share one basic block");
    std::unique_ptr<Statement> entryStatement(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            MemoryLocation(MemoryDomain::FIRST_REGISTER + 51, 0, 32))),
        constant(32, 2)));
    entryStatement->setInstruction(&entryInstruction);
    block->pushBack(std::move(entryStatement));

    BasicBlock *oldSuccessor = program.createBasicBlock(0x1002);
    block->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(oldSuccessor))));

    BasicBlock *entry = program.refineFunctionEntry(0x1001);
    check(entry != nullptr && entry != block &&
              program.isFunctionEntry(0x1001),
          "late function evidence must create a distinct entry block");
    check(block->getJump() &&
              block->getJump()->thenTarget().basicBlock() == entry,
          "splitting finalized IR must preserve predecessor fall-through");
    check(entry->getJump() &&
              entry->getJump()->thenTarget().basicBlock() == oldSuccessor,
          "the split entry must retain the original outgoing edge");

    CFG cfg(program.basicBlocks());
    check(cfg.getSuccessors(block).size() == 1 &&
              cfg.getSuccessors(block).front() == entry,
          "the refined Program CFG must contain the materialized edge");
}

void testLateEntryInsideIrlessTailPreservesFallthrough() {
    Program program;
    TestInstruction materialInstruction(0x2000, 1);
    TestInstruction irlessInstruction(0x2001, 1);

    BasicBlock *block = program.getBasicBlockForInstruction(
        &materialInstruction);
    std::unique_ptr<Statement> statement(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            MemoryLocation(MemoryDomain::FIRST_REGISTER + 52, 0, 32))),
        constant(32, 1)));
    statement->setInstruction(&materialInstruction);
    block->pushBack(std::move(statement));

    check(program.getBasicBlockForInstruction(
              &irlessInstruction) == block,
          "an IR-less instruction must still extend its containing range");
    BasicBlock *successor = program.createBasicBlock(0x2002);
    block->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(successor))));

    BasicBlock *entry = program.refineFunctionEntry(0x2001);
    check(entry && entry != block &&
              program.isFunctionEntry(0x2001),
          "an entry in an IR-less tail must create a distinct block");
    check(block->getJump() &&
              block->getJump()->thenTarget().basicBlock() == entry,
          "the material predecessor must fall through to the IR-less entry");
    check(entry->getJump() &&
              entry->getJump()->thenTarget().basicBlock() == successor,
          "the synthetic successor edge must move with the IR-less tail");

    CFG cfg(program.basicBlocks());
    check(cfg.getSuccessors(block).size() == 1 &&
              cfg.getSuccessors(block).front() == entry &&
              cfg.getSuccessors(entry).size() == 1 &&
              cfg.getSuccessors(entry).front() == successor,
          "an IR-less late entry must remain connected on both sides");
}

void testKnownIrlessFunctionEntryIsPreserved() {
    Program program;
    TestInstruction firstNop(0x2100, 1);
    TestInstruction secondNop(0x2101, 1);

    BasicBlock *entry = program.getBasicBlockForInstruction(&firstNop);
    check(program.getBasicBlockForInstruction(&secondNop) == entry &&
              entry->statements().empty(),
          "the fixture must contain a decoded range with no semantic IR");
    program.addFunctionEntry(0x2100);

    Functions functions;
    FunctionsGenerator().makeFunctions(program, functions);
    check(functions.list().size() == 1 &&
              functions.list().front()->entry() &&
              functions.list().front()->entry()->address() &&
              *functions.list().front()->entry()->address() == 0x2100,
          "a proved entry made only of IR-less instructions must survive function generation");

    Program anonymousProgram;
    anonymousProgram.getBasicBlockForInstruction(&firstNop);
    Functions anonymousFunctions;
    FunctionsGenerator().makeFunctions(
        anonymousProgram, anonymousFunctions);
    check(anonymousFunctions.list().empty(),
          "an anonymous IR-less range must not manufacture a function");
}

void testDirectCallBoundaryPreventsFunctionMerging() {
    Program program;
    TestInstruction callerInstruction(0x2200, 1);
    TestInstruction calleeInstruction(0x2201, 1);

    BasicBlock *caller = program.getBasicBlockForInstruction(
        &callerInstruction);
    std::unique_ptr<Statement> callerStatement(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            MemoryLocation(MemoryDomain::FIRST_REGISTER + 53, 0, 32))),
        constant(32, 1)));
    callerStatement->setInstruction(&callerInstruction);
    caller->pushBack(std::move(callerStatement));

    BasicBlock *callee = program.createBasicBlock(0x2201);
    program.getBasicBlockForInstruction(&calleeInstruction);
    std::unique_ptr<Statement> calleeStatement(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            MemoryLocation(MemoryDomain::FIRST_REGISTER + 54, 0, 32))),
        constant(32, 2)));
    calleeStatement->setInstruction(&calleeInstruction);
    callee->pushBack(std::move(calleeStatement));
    caller->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(callee))));

    program.addFunctionEntry(0x2200);
    program.addCalledAddress(0x2201);
    check(program.isFunctionEntry(0x2201),
          "a proved direct call target must become a function entry");

    Functions functions;
    FunctionsGenerator().makeFunctions(program, functions);
    check(functions.list().size() == 2,
          "a CFG edge must not merge two proved function entries");
    for (const Function *function : functions.list()) {
        check(function->basicBlocks().size() == 1,
              "each proved entry must own only its side of the boundary");
    }
}

Statement *addStackAdjustment(
        BasicBlock *block, const MemoryLocation &stackPointer,
        ConstantValue amount, bool subtract,
        const arch::Instruction *instruction) {
    std::unique_ptr<Statement> statement(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(stackPointer)),
        std::unique_ptr<Term>(new BinaryOperator(
            subtract ? BinaryOperator::SUB : BinaryOperator::ADD,
            std::unique_ptr<Term>(new MemoryLocationAccess(stackPointer)),
            constant(stackPointer.size<SmallBitSize>(), amount),
            stackPointer.size<SmallBitSize>()))));
    statement->setInstruction(instruction);
    return block->pushBack(std::move(statement));
}

Term *addStackStore(
        BasicBlock *block, const MemoryLocation &stackPointer,
        ByteSize byteOffset, ConstantValue value,
        const arch::Instruction *instruction) {
    std::unique_ptr<Term> address(new MemoryLocationAccess(stackPointer));
    if (byteOffset != 0) {
        address.reset(new BinaryOperator(
            BinaryOperator::ADD, std::move(address),
            constant(stackPointer.size<SmallBitSize>(), byteOffset),
            stackPointer.size<SmallBitSize>()));
    }
    std::unique_ptr<Term> destination(new Dereference(
        std::move(address), MemoryDomain::MEMORY, 32));
    Term *result = destination.get();
    std::unique_ptr<Statement> statement(new Assignment(
        std::move(destination), constant(32, value)));
    statement->setInstruction(instruction);
    block->pushBack(std::move(statement));
    return result;
}

void addSemanticPush(
        BasicBlock *block, const MemoryLocation &stackPointer,
        ConstantValue value, const arch::Instruction *instruction) {
    addStackAdjustment(block, stackPointer, 4, true, instruction);
    addStackStore(block, stackPointer, 0, value, instruction);
}

enum CallFrameFixtureKind {
    COMPLETE_PUSH_FRAME,
    FOLDED_FRAME_TEARDOWN,
    GAPPED_PUSH_FRAME,
    PREALLOCATED_OUTGOING_FRAME,
    DELAYED_CALLER_CLEANUP
};

boost::optional<ByteSize> analyzeCallFrameFixture(
        CallFrameFixtureKind kind,
        std::size_t *recoveredArgumentCount = nullptr,
        bool addExternalStub = false,
        bool markExternalStubOpaque = false) {
    const ConstantValue targetAddress = 0x7700;
    TestArchitecture architecture;
    TestStackConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    Function externalStub;
    if (addExternalStub) {
        std::unique_ptr<BasicBlock> stubBlockStorage(
            new BasicBlock(static_cast<ByteAddr>(targetAddress)));
        BasicBlock *stubBlock = stubBlockStorage.get();
        externalStub.addBasicBlock(std::move(stubBlockStorage));
        externalStub.setEntry(stubBlock);
        stubBlock->pushBack(std::unique_ptr<Statement>(new Halt()));
    }

    TestInstruction firstSetupInstruction(0x1000, 1);
    TestInstruction secondSetupInstruction(0x1001, 1);
    TestInstruction callInstruction(0x1002, 5);
    TestInstruction interveningInstruction(0x1007, 1);
    TestInstruction cleanupInstruction(0x1008, 3);

    if (kind == PREALLOCATED_OUTGOING_FRAME) {
        addStackAdjustment(
            block, convention.stackPointerLocation, 8, true,
            &firstSetupInstruction);
        addStackStore(
            block, convention.stackPointerLocation, 0, 0x11,
            &secondSetupInstruction);
        addStackStore(
            block, convention.stackPointerLocation, 4, 0x22,
            &secondSetupInstruction);
    } else if (kind == GAPPED_PUSH_FRAME) {
        /* Reserve the high slot without defining it, then push only the low
         * slot. The cleanup size alone must not fill this evidence gap. */
        addStackAdjustment(
            block, convention.stackPointerLocation, 4, true,
            &firstSetupInstruction);
        addSemanticPush(
            block, convention.stackPointerLocation, 0x22,
            &secondSetupInstruction);
    } else {
        addSemanticPush(
            block, convention.stackPointerLocation, 0x11,
            &firstSetupInstruction);
        if (kind != FOLDED_FRAME_TEARDOWN) {
            addSemanticPush(
                block, convention.stackPointerLocation, 0x22,
                &secondSetupInstruction);
        }
    }

    /* Model the architecture's call sequence: push return address, execute
     * the call, then remove the return-address slot. */
    addStackAdjustment(
        block, convention.stackPointerLocation, 4, true,
        &callInstruction);
    {
        std::unique_ptr<Term> destination(new Dereference(
            std::unique_ptr<Term>(new MemoryLocationAccess(
                convention.stackPointerLocation)),
            MemoryDomain::MEMORY, 32));
        std::unique_ptr<Statement> statement(new Assignment(
            std::move(destination),
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::RETURN_ADDRESS, 32))));
        statement->setInstruction(&callInstruction);
        block->pushBack(std::move(statement));
    }
    std::unique_ptr<Call> callStorage(new Call(
        constant(32, targetAddress)));
    Call *call = callStorage.get();
    callStorage->setInstruction(&callInstruction);
    block->pushBack(std::move(callStorage));
    addStackAdjustment(
        block, convention.stackPointerLocation, 4, false,
        &callInstruction);

    if (kind == DELAYED_CALLER_CLEANUP) {
        std::unique_ptr<Statement> intervening(new Assignment(
            std::unique_ptr<Term>(new MemoryLocationAccess(
                MemoryLocation(
                    MemoryDomain::FIRST_REGISTER + 45, 0, 32))),
            constant(32, 7)));
        intervening->setInstruction(&interveningInstruction);
        block->pushBack(std::move(intervening));
    }
    addStackAdjustment(
        block, convention.stackPointerLocation, 8, false,
        &cleanupInstruction);
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(targetAddress)),
        &convention);
    if (markExternalStubOpaque) {
        /* Model the conflicting fact produced when a tail-jump-only thunk is
         * analyzed before its relocation-backed external identity is known. */
        conventions.setConflictingReturnStackCleanup(
            calling::CalleeId(calling::EntryAddress(targetAddress)));
        conventions.setExternalBodyOpaque(
            calling::CalleeId(calling::EntryAddress(targetAddress)));
        /* Re-analysis must not reintroduce body evidence for an opaque
         * forwarding boundary. */
        conventions.setConflictingReturnStackCleanup(
            calling::CalleeId(calling::EntryAddress(targetAddress)));
    }
    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);
    std::unique_ptr<Dataflow> dataflow(new Dataflow());
    hooks.instrument(&function, dataflow.get());

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(
        *dataflow, &architecture, canceled, log).analyze(cfg);
    check(dataflow->converged(),
          "the call-frame fixture must reach a dataflow fixpoint");

    const calling::CallHook *hook = hooks.getCallHook(call);
    check(hook != nullptr && hook->snapshotStatement() != nullptr,
          "the unknown external call must retain an inference snapshot");
    const boost::optional<ByteSize> result =
        calling::CallFrameAnalyzer::inferCallerCleanupArgumentSize(
            call, &convention, hook, *dataflow);

    if (recoveredArgumentCount) {
        std::unique_ptr<liveness::Liveness> liveness(
            new liveness::Liveness());
        liveness::LivenessAnalyzer(
            *liveness, &function, *dataflow, &architecture, nullptr,
            hooks, &signatures, log).analyze();

        dflow::Dataflows dataflows;
        dataflows.emplace(
            &function,
            std::unique_ptr<const Dataflow>(std::move(dataflow)));
        liveness::Livenesses livenesses;
        livenesses.emplace(
            &function,
            std::unique_ptr<const liveness::Liveness>(
                std::move(liveness)));

        if (addExternalStub) {
            std::unique_ptr<Dataflow> stubDataflow(new Dataflow());
            hooks.instrument(&externalStub, stubDataflow.get());
            CFG stubCfg(externalStub.basicBlocks());
            DataflowAnalyzer(
                *stubDataflow, &architecture, canceled, log).analyze(
                    stubCfg);
            check(stubDataflow->converged(),
                  "the external-stub fixture must reach a dataflow fixpoint");

            std::unique_ptr<liveness::Liveness> stubLiveness(
                new liveness::Liveness());
            liveness::LivenessAnalyzer(
                *stubLiveness, &externalStub, *stubDataflow,
                &architecture, nullptr, hooks, &signatures,
                log).analyze();
            dataflows.emplace(
                &externalStub,
                std::unique_ptr<const Dataflow>(
                    std::move(stubDataflow)));
            livenesses.emplace(
                &externalStub,
                std::unique_ptr<const liveness::Liveness>(
                    std::move(stubLiveness)));
        }
        calling::SignatureAnalyzer(
            signatures, dataflows, hooks, livenesses,
            canceled, log).analyze();

        const auto &signature = signatures.getSignature(
            static_cast<ByteAddr>(targetAddress));
        *recoveredArgumentCount =
            signature ? signature->arguments().size() : 0;
    }
    return result;
}

void testCallerCleanupCallFrameInference() {
    std::size_t recoveredArgumentCount = 0;
    const boost::optional<ByteSize> complete =
        analyzeCallFrameFixture(
            COMPLETE_PUSH_FRAME, &recoveredArgumentCount);
    check(complete && *complete == 8,
          "a fully covered semantic push/restore frame must expose its exact extent");
    check(recoveredArgumentCount == 2,
          "signature reconstruction must consume the proved call-frame extent");

    recoveredArgumentCount = 1;
    analyzeCallFrameFixture(
        COMPLETE_PUSH_FRAME, &recoveredArgumentCount, true, false);
    check(recoveredArgumentCount == 0,
          "an ordinary local body must suppress caller-only ABI inference");
    analyzeCallFrameFixture(
        COMPLETE_PUSH_FRAME, &recoveredArgumentCount, true, true);
    check(recoveredArgumentCount == 2,
          "an explicitly opaque external thunk must not suppress call-site evidence");
    check(!analyzeCallFrameFixture(FOLDED_FRAME_TEARDOWN),
          "cleanup larger than the pushed range must not absorb caller locals");
    recoveredArgumentCount = 1;
    check(!analyzeCallFrameFixture(
              GAPPED_PUSH_FRAME, &recoveredArgumentCount),
          "an undefined slot inside the restored range must reject the extent");
    check(recoveredArgumentCount == 0,
          "a rejected extent must not leak stack arguments into the signature");
    check(!analyzeCallFrameFixture(PREALLOCATED_OUTGOING_FRAME),
          "preallocated outgoing storage must not be guessed to contain arguments");
    check(!analyzeCallFrameFixture(DELAYED_CALLER_CLEANUP),
          "a later epilogue-style SP update must not be treated as immediate call cleanup");
}

void runSignatureInferencePass(
        Function &function, const TestArchitecture &architecture,
        calling::Hooks &hooks, calling::Signatures &signatures) {
    std::unique_ptr<Dataflow> dataflow(new Dataflow());
    hooks.instrument(&function, dataflow.get());

    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(
        *dataflow, &architecture, canceled, log).analyze(
            CFG(function.basicBlocks()));
    hooks.finalizeInstrumentation(&function, *dataflow);
    check(dataflow->converged(),
          "the repeated signature pass must reach a dataflow fixpoint");

    std::unique_ptr<liveness::Liveness> liveness(
        new liveness::Liveness());
    liveness::LivenessAnalyzer(
        *liveness, &function, *dataflow, &architecture, nullptr,
        hooks, &signatures, log).analyze();

    dflow::Dataflows dataflows;
    dataflows.emplace(
        &function,
        std::unique_ptr<const Dataflow>(std::move(dataflow)));
    liveness::Livenesses livenesses;
    livenesses.emplace(
        &function,
        std::unique_ptr<const liveness::Liveness>(
            std::move(liveness)));

    signatures.beginInferenceUpdate();
    try {
        calling::SignatureAnalyzer(
            signatures, dataflows, hooks, livenesses,
            canceled, log).analyze();
        signatures.finishInferenceUpdate();
    } catch (...) {
        signatures.cancelInferenceUpdate();
        throw;
    }
}

bool hasOnlyRegisterArgument(
        const std::shared_ptr<calling::FunctionSignature> &signature,
        const MemoryLocation &location) {
    if (!signature || signature->arguments().size() != 1) {
        return false;
    }
    const auto access =
        signature->arguments().front()->asMemoryLocationAccess();
    return access && access->memoryLocation() == location;
}

void testInferredFunctionSignatureIsRevalidatedAcrossPasses() {
    TestArchitecture architecture;
    TestRegisterInferenceConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    std::unique_ptr<Statement> argumentReadStorage(new Touch(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            convention.argumentLocation)), Term::READ));
    Statement *argumentRead = argumentReadStorage.get();
    block->pushBack(std::move(argumentReadStorage));

    std::unique_ptr<Statement> returnDefinitionStorage(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            convention.returnLocation)), constant(32, 0x41)));
    Statement *returnDefinition = returnDefinitionStorage.get();
    block->pushBack(std::move(returnDefinitionStorage));
    block->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(
        std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::RETURN_ADDRESS, 32))))));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);

    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        const auto &signature = signatures.getSignature(
            &function, calling::SignatureSource::INFERRED);
        check(hasOnlyRegisterArgument(
                  signature, convention.argumentLocation),
              "an inferred formal argument disappeared on a later semantic pass");
        const auto returnAccess = signature && signature->returnValue() ?
            signature->returnValue()->asMemoryLocationAccess() : nullptr;
        check(returnAccess &&
                  returnAccess->memoryLocation() == convention.returnLocation,
              "an inferred body return disappeared on a later semantic pass");
    }

    block->erase(argumentRead);
    block->erase(returnDefinition);
    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &withoutEvidence = signatures.getSignature(
        &function, calling::SignatureSource::INFERRED);
    check(withoutEvidence && withoutEvidence->arguments().empty() &&
              !withoutEvidence->returnValue(),
          "synthetic entry/return hooks kept a stale inferred signature alive");

    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &stableEmpty = signatures.getSignature(
        &function, calling::SignatureSource::INFERRED);
    check(stableEmpty && stableEmpty->arguments().empty() &&
              !stableEmpty->returnValue(),
          "removed function evidence was recreated by a later hook pass");
}

void testWideReturnDefinitionKeepsUnusedLowHalfAcrossPasses() {
    TestArchitecture architecture;
    TestRegisterInferenceConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    const MemoryLocation wideReturn(
        convention.returnLocation.domain(),
        convention.returnLocation.addr(), 64);
    const MemoryLocation highHalf(
        convention.returnLocation.domain(),
        convention.returnLocation.endAddr(), 32);
    const MemoryLocation globalSink(
        MemoryDomain::MEMORY, 0xb000, 32);
    addDefinition(
        block, wideReturn,
        constant(64, 0x5152535455565758ULL));
    addReadDefinition(block, highHalf, globalSink);
    block->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(
        std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::RETURN_ADDRESS, 32))))));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);

    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        const auto &signature = signatures.getSignature(
            &function, calling::SignatureSource::INFERRED);
        const auto returnAccess = signature && signature->returnValue() ?
            signature->returnValue()->asMemoryLocationAccess() : nullptr;
        check(returnAccess &&
                  returnAccess->memoryLocation() ==
                      convention.returnLocation,
              "a live high-half consumer suppressed the unused low-half return");
    }
}

void testSharedReturnDefinitionAcrossTwoReturnsIsStable() {
    TestArchitecture architecture;
    TestRegisterInferenceConvention convention;
    Function function;
    BasicBlock *entry = addBlock(function);
    BasicBlock *leftReturn = addBlock(function);
    BasicBlock *rightReturn = addBlock(function);
    function.setEntry(entry);

    addDefinition(
        entry, convention.returnLocation, constant(32, 0x41));
    entry->pushBack(std::unique_ptr<Statement>(new Jump(
        constant(1, 1), JumpTarget(leftReturn), JumpTarget(rightReturn))));
    leftReturn->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(
        std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::RETURN_ADDRESS, 32))))));
    rightReturn->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(
        std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::RETURN_ADDRESS, 32))))));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);

    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        const auto &signature = signatures.getSignature(
            &function, calling::SignatureSource::INFERRED);
        const auto returnAccess = signature && signature->returnValue() ?
            signature->returnValue()->asMemoryLocationAccess() : nullptr;
        check(returnAccess &&
                  returnAccess->memoryLocation() ==
                      convention.returnLocation,
              "one return hook treated another return's observation as a real use");
    }
}

void testInferredCallReturnIsRevalidatedAcrossPasses() {
    const ByteAddr targetAddress = 0x7850;
    TestArchitecture architecture;
    TestRegisterInferenceConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    std::unique_ptr<Call> callStorage(new Call(
        constant(32, targetAddress)));
    Call *call = callStorage.get();
    block->pushBack(std::move(callStorage));
    std::unique_ptr<Statement> returnReadStorage(new Touch(
        std::unique_ptr<Term>(new MemoryLocationAccess(
            convention.returnLocation)), Term::READ));
    Statement *returnRead = returnReadStorage.get();
    block->pushBack(std::move(returnReadStorage));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(targetAddress)),
        &convention);
    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);

    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        const auto &callSignature = signatures.getSignature(
            call, calling::SignatureSource::INFERRED);
        const auto &targetSignature = signatures.getSignature(
            targetAddress, calling::SignatureSource::INFERRED);
        const auto callReturn =
            callSignature && callSignature->returnValue() ?
                callSignature->returnValue()->asMemoryLocationAccess() :
                nullptr;
        const auto targetReturn =
            targetSignature && targetSignature->returnValue() ?
                targetSignature->returnValue()->asMemoryLocationAccess() :
                nullptr;
        check(callReturn && targetReturn &&
                  callReturn->memoryLocation() ==
                      convention.returnLocation &&
                  targetReturn->memoryLocation() ==
                      convention.returnLocation,
              "an inferred call return disappeared on a later semantic pass");
    }

    block->erase(returnRead);
    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &withoutUse = signatures.getSignature(
        call, calling::SignatureSource::INFERRED);
    check(withoutUse && !withoutUse->returnValue(),
          "a synthetic call return kept stale result evidence alive");

    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &stableWithoutUse = signatures.getSignature(
        call, calling::SignatureSource::INFERRED);
    check(stableWithoutUse && !stableWithoutUse->returnValue(),
          "a removed call-result use was recreated by a later hook pass");
}

std::shared_ptr<Term> stackArgumentTerm(
        const MemoryLocation &stackPointer, ByteSize byteOffset) {
    return std::shared_ptr<Term>(new Dereference(
        std::unique_ptr<Term>(new BinaryOperator(
            BinaryOperator::ADD,
            std::unique_ptr<Term>(new MemoryLocationAccess(stackPointer)),
            constant(stackPointer.size<SmallBitSize>(), byteOffset),
            stackPointer.size<SmallBitSize>())),
        MemoryDomain::MEMORY, 32));
}

bool isStackArgumentAt(
        const std::shared_ptr<const Term> &term,
        const MemoryLocation &stackPointer, ByteSize byteOffset) {
    const Dereference *dereference = term ? term->asDereference() : nullptr;
    const BinaryOperator *address = dereference ?
        dereference->address()->asBinaryOperator() : nullptr;
    const MemoryLocationAccess *base = address ?
        address->left()->asMemoryLocationAccess() : nullptr;
    const Constant *offset = address ?
        address->right()->asConstant() : nullptr;
    return dereference && dereference->domain() == MemoryDomain::MEMORY &&
        base && base->memoryLocation() == stackPointer && offset &&
        offset->value().value() ==
            static_cast<ConstantValue>(byteOffset);
}

std::shared_ptr<calling::CallSignature> makeVariadicStackCallSignature(
        const MemoryLocation &stackPointer) {
    std::vector<calling::ParameterDescription> parameters;
    parameters.push_back(calling::ParameterDescription(
        QLatin1String("fixed"),
        calling::TypeDescription(
            calling::TypeDescription::INTEGER, 32, false),
        calling::ParameterDescription::PointeeAccess::NONE));
    const auto prototype =
        std::make_shared<const calling::FunctionPrototype>(
            calling::TypeDescription(
                calling::TypeDescription::VOID, 0, false),
            std::move(parameters), QString(), QString(), true,
            QString(), true);
    std::shared_ptr<calling::CallSignature> signature(
        new calling::CallSignature());
    signature->arguments().push_back(stackArgumentTerm(stackPointer, 4));
    signature->arguments().push_back(stackArgumentTerm(stackPointer, 8));
    signature->setPrototype(prototype);
    return signature;
}

void testVariadicStackTailWithoutExtentIsRevalidated() {
    const ConstantValue targetAddress = 0x7900;
    TestArchitecture architecture;
    TestStackConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    TestInstruction setupInstruction(0x1200, 1);
    TestInstruction callInstruction(0x1201, 5);
    addStackStore(
        block, convention.stackPointerLocation, 4, 0x51,
        &setupInstruction);
    std::unique_ptr<Term> wideTailAddress(new BinaryOperator(
        BinaryOperator::ADD,
        std::unique_ptr<Term>(new MemoryLocationAccess(
            convention.stackPointerLocation)),
        constant(convention.stackPointerLocation.size<SmallBitSize>(), 8),
        convention.stackPointerLocation.size<SmallBitSize>()));
    std::unique_ptr<Statement> tailDefinitionStorage(new Assignment(
        std::unique_ptr<Term>(new Dereference(
            std::move(wideTailAddress), MemoryDomain::MEMORY, 64)),
        constant(64, 0x52535455)));
    Statement *tailDefinition = tailDefinitionStorage.get();
    tailDefinitionStorage->setInstruction(&setupInstruction);
    block->pushBack(std::move(tailDefinitionStorage));

    std::unique_ptr<Call> callStorage(new Call(
        constant(32, targetAddress)));
    Call *call = callStorage.get();
    callStorage->setInstruction(&callInstruction);
    block->pushBack(std::move(callStorage));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    const calling::CalleeId callSiteId(
        calling::CallAddress(callInstruction.addr()));
    conventions.setExternalConvention(callSiteId, &convention);
    check(!conventions.hasExternalStackArgumentsSizeBinding(callSiteId),
          "the variadic stack-tail fixture must not have an argument extent");

    std::vector<calling::ParameterDescription> parameters;
    parameters.push_back(calling::ParameterDescription(
        QLatin1String("fixed"),
        calling::TypeDescription(
            calling::TypeDescription::INTEGER, 32, false),
        calling::ParameterDescription::PointeeAccess::NONE));
    const auto prototype =
        std::make_shared<const calling::FunctionPrototype>(
            calling::TypeDescription(
                calling::TypeDescription::VOID, 0, false),
            std::move(parameters), QString(), QString(), true,
            QString(), true);
    std::shared_ptr<calling::CallSignature> externalSignature(
        new calling::CallSignature());
    externalSignature->arguments().push_back(stackArgumentTerm(
        convention.stackPointerLocation, 4));
    externalSignature->arguments().push_back(stackArgumentTerm(
        convention.stackPointerLocation, 8));
    externalSignature->setPrototype(prototype);

    calling::Signatures signatures;
    signatures.setSignature(
        call, externalSignature, calling::SignatureSource::EXTERNAL);
    calling::Hooks hooks(conventions, signatures);

    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        const auto &inferred = signatures.getSignature(
            call, calling::SignatureSource::INFERRED);
        check(inferred != nullptr,
              "variadic stack-tail inference produced no call signature");
        check(inferred->argumentEvidence() ==
                  calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL,
              "variadic stack-tail inference lost its evidence provenance");
        check(!inferred->arguments().empty(),
              "a proved variadic stack tail without a declared extent was lost");
        check(inferred->arguments().size() == 1,
              "variadic tail inference retained an unrelated stack slot");
        check(isStackArgumentAt(
                  inferred->arguments().front(),
                  convention.stackPointerLocation, 8),
              "a variadic stack tail was normalized to the wrong slot");
    }

    block->erase(tailDefinition);
    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &withoutTail = signatures.getSignature(
        call, calling::SignatureSource::INFERRED);
    check(withoutTail && withoutTail->arguments().empty() &&
              withoutTail->argumentEvidence() ==
                  calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL,
          "a removed variadic stack tail remained self-sustaining");

    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &stableWithoutTail = signatures.getSignature(
        call, calling::SignatureSource::INFERRED);
    check(stableWithoutTail && stableWithoutTail->arguments().empty(),
          "a synthetic tail read recreated removed stack evidence");
}

void testWideFixedAndVariadicStoreIsRevalidatedAcrossPasses() {
    const ConstantValue targetAddress = 0x7910;
    TestArchitecture architecture;
    TestStackConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    TestInstruction setupInstruction(0x1210, 1);
    TestInstruction callInstruction(0x1211, 5);
    std::unique_ptr<Term> wideAddress(new BinaryOperator(
        BinaryOperator::ADD,
        std::unique_ptr<Term>(new MemoryLocationAccess(
            convention.stackPointerLocation)),
        constant(convention.stackPointerLocation.size<SmallBitSize>(), 4),
        convention.stackPointerLocation.size<SmallBitSize>()));
    std::unique_ptr<Statement> wideDefinitionStorage(new Assignment(
        std::unique_ptr<Term>(new Dereference(
            std::move(wideAddress), MemoryDomain::MEMORY, 64)),
        constant(64, 0x5152535455565758ULL)));
    Statement *wideDefinition = wideDefinitionStorage.get();
    wideDefinitionStorage->setInstruction(&setupInstruction);
    block->pushBack(std::move(wideDefinitionStorage));

    std::unique_ptr<Call> callStorage(new Call(
        constant(32, targetAddress)));
    Call *call = callStorage.get();
    callStorage->setInstruction(&callInstruction);
    block->pushBack(std::move(callStorage));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    const calling::CalleeId callSiteId(
        calling::CallAddress(callInstruction.addr()));
    conventions.setExternalConvention(callSiteId, &convention);
    check(!conventions.hasExternalStackArgumentsSizeBinding(callSiteId),
          "the spanning variadic fixture must not have an argument extent");

    calling::Signatures signatures;
    signatures.setSignature(
        call, makeVariadicStackCallSignature(
                  convention.stackPointerLocation),
        calling::SignatureSource::EXTERNAL);
    calling::Hooks hooks(conventions, signatures);

    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        const auto &inferred = signatures.getSignature(
            call, calling::SignatureSource::INFERRED);
        check(inferred &&
                  inferred->argumentEvidence() ==
                      calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL &&
                  inferred->arguments().size() == 1 &&
                  isStackArgumentAt(
                      inferred->arguments().front(),
                      convention.stackPointerLocation, 8),
              "a wide fixed-and-tail store lost its variadic subrange");
    }

    block->erase(wideDefinition);
    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &withoutDefinition = signatures.getSignature(
        call, calling::SignatureSource::INFERRED);
    check(withoutDefinition && withoutDefinition->arguments().empty() &&
              withoutDefinition->argumentEvidence() ==
                  calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL,
          "a deleted wide store left stale variadic-tail evidence");

    runSignatureInferencePass(
        function, architecture, hooks, signatures);
    const auto &stableWithoutDefinition = signatures.getSignature(
        call, calling::SignatureSource::INFERRED);
    check(stableWithoutDefinition &&
              stableWithoutDefinition->arguments().empty(),
          "a synthetic tail observation recreated a deleted wide store");
}

void testSharedVariadicDefinitionAcrossTwoCallsIsStable() {
    const ConstantValue targetAddress = 0x7920;
    TestArchitecture architecture;
    TestStackConvention convention;
    Function function;
    BasicBlock *entry = addBlock(function);
    BasicBlock *leftCallBlock = addBlock(function);
    BasicBlock *rightCallBlock = addBlock(function);
    function.setEntry(entry);

    TestInstruction setupInstruction(0x1220, 1);
    TestInstruction leftCallInstruction(0x1221, 5);
    TestInstruction rightCallInstruction(0x1226, 5);
    addStackStore(
        entry, convention.stackPointerLocation, 8, 0x61,
        &setupInstruction);
    entry->pushBack(std::unique_ptr<Statement>(new Jump(
        constant(1, 1), JumpTarget(leftCallBlock),
        JumpTarget(rightCallBlock))));

    auto appendCall = [&](BasicBlock *block,
                          const TestInstruction *instruction) -> Call * {
        std::unique_ptr<Call> storage(new Call(
            constant(32, targetAddress)));
        Call *call = storage.get();
        storage->setInstruction(instruction);
        block->pushBack(std::move(storage));
        block->pushBack(std::unique_ptr<Statement>(new Halt()));
        return call;
    };
    Call *leftCall = appendCall(
        leftCallBlock, &leftCallInstruction);
    Call *rightCall = appendCall(
        rightCallBlock, &rightCallInstruction);

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    conventions.setExternalConvention(
        calling::CalleeId(calling::CallAddress(
            leftCallInstruction.addr())), &convention);
    conventions.setExternalConvention(
        calling::CalleeId(calling::CallAddress(
            rightCallInstruction.addr())), &convention);

    calling::Signatures signatures;
    signatures.setSignature(
        leftCall, makeVariadicStackCallSignature(
                      convention.stackPointerLocation),
        calling::SignatureSource::EXTERNAL);
    signatures.setSignature(
        rightCall, makeVariadicStackCallSignature(
                       convention.stackPointerLocation),
        calling::SignatureSource::EXTERNAL);
    calling::Hooks hooks(conventions, signatures);

    const Call *calls[] = { leftCall, rightCall };
    for (int pass = 0; pass < 3; ++pass) {
        runSignatureInferencePass(
            function, architecture, hooks, signatures);
        foreach (const Call *call, calls) {
            const auto &inferred = signatures.getSignature(
                call, calling::SignatureSource::INFERRED);
            check(inferred &&
                      inferred->argumentEvidence() ==
                          calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL &&
                      inferred->arguments().size() == 1 &&
                      isStackArgumentAt(
                          inferred->arguments().front(),
                          convention.stackPointerLocation, 8),
                  "one call hook treated another call's observation as a real use");
        }
    }
}

void testCallSpecificVariadicArguments() {
    const ConstantValue targetAddress = 0x7800;
    TestArchitecture architecture;
    TestStackConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    TestInstruction shortSetupInstruction(0x1100, 1);
    TestInstruction shortCallInstruction(0x1101, 5);
    TestInstruction shortCleanupInstruction(0x1106, 3);
    TestInstruction longFirstSetupInstruction(0x1109, 1);
    TestInstruction longSecondSetupInstruction(0x110a, 1);
    TestInstruction longCallInstruction(0x110b, 5);
    TestInstruction longCleanupInstruction(0x1110, 3);

    auto appendCall = [&](const arch::Instruction *instruction) -> Call * {
        addStackAdjustment(
            block, convention.stackPointerLocation, 4, true,
            instruction);
        std::unique_ptr<Term> returnAddressDestination(new Dereference(
            std::unique_ptr<Term>(new MemoryLocationAccess(
                convention.stackPointerLocation)),
            MemoryDomain::MEMORY, 32));
        std::unique_ptr<Statement> returnAddressWrite(new Assignment(
            std::move(returnAddressDestination),
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::RETURN_ADDRESS, 32)),
            Assignment::CONTROL_FLOW_STATE));
        returnAddressWrite->setInstruction(instruction);
        block->pushBack(std::move(returnAddressWrite));

        std::unique_ptr<Call> callStorage(new Call(
            constant(32, targetAddress)));
        Call *call = callStorage.get();
        callStorage->setInstruction(instruction);
        block->pushBack(std::move(callStorage));
        addStackAdjustment(
            block, convention.stackPointerLocation, 4, false,
            instruction);
        return call;
    };

    addSemanticPush(
        block, convention.stackPointerLocation, 0x11,
        &shortSetupInstruction);
    Call *shortCall = appendCall(&shortCallInstruction);
    addStackAdjustment(
        block, convention.stackPointerLocation, 4, false,
        &shortCleanupInstruction);

    addSemanticPush(
        block, convention.stackPointerLocation, 0x21,
        &longFirstSetupInstruction);
    addSemanticPush(
        block, convention.stackPointerLocation, 0x22,
        &longSecondSetupInstruction);
    Call *longCall = appendCall(&longCallInstruction);
    addStackAdjustment(
        block, convention.stackPointerLocation, 8, false,
        &longCleanupInstruction);
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &convention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(targetAddress)),
        &convention);
    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);
    std::unique_ptr<Dataflow> dataflow(new Dataflow());
    hooks.instrument(&function, dataflow.get());

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(
        *dataflow, &architecture, canceled, log).analyze(cfg);
    check(dataflow->converged(),
          "the mixed-arity fixture must reach a dataflow fixpoint");

    std::unique_ptr<liveness::Liveness> liveness(
        new liveness::Liveness());
    liveness::LivenessAnalyzer(
        *liveness, &function, *dataflow, &architecture, nullptr,
        hooks, &signatures, log).analyze();

    dflow::Dataflows dataflows;
    dataflows.emplace(
        &function, std::unique_ptr<const Dataflow>(std::move(dataflow)));
    liveness::Livenesses livenesses;
    livenesses.emplace(
        &function,
        std::unique_ptr<const liveness::Liveness>(
            std::move(liveness)));
    calling::SignatureAnalyzer(
        signatures, dataflows, hooks, livenesses,
        canceled, log).analyze();

    const auto &functionSignature = signatures.getSignature(
        static_cast<ByteAddr>(targetAddress));
    const auto &shortSignature = signatures.getSignature(shortCall);
    const auto &longSignature = signatures.getSignature(longCall);
    check(functionSignature &&
              functionSignature->arguments().size() == 1 &&
              functionSignature->variadic(),
          "only the argument present at every call may become the common variadic prefix");
    check(shortSignature &&
              shortSignature->arguments().size() == 1,
          "a short variadic call must not inherit arguments from a longer call");
    check(longSignature &&
              longSignature->arguments().size() == 2,
          "a long variadic call must retain its proved call-specific suffix");
}

void testCallClobberContract() {
    TestConvention convention;
    calling::CallHook hook(&convention, nullptr, boost::none);

    check(hook.snapshotStatement() != nullptr,
          "an unknown signature must retain its inference snapshot");
    check(hook.pointeeReadSnapshotStatement() == nullptr,
          "an unknown signature must not reuse the inference snapshot for pointee reads");

    std::size_t index = 0;
    std::size_t volatileWrite = (std::numeric_limits<std::size_t>::max)();
    std::size_t returnWrite = (std::numeric_limits<std::size_t>::max)();
    foreach (const Statement *statement, hook.patch().statements()) {
        const Assignment *assignment = statement->asAssignment();
        if (assignment) {
            const MemoryLocationAccess *left =
                assignment->left()->asMemoryLocationAccess();
            check(left != nullptr,
                  "call-hook register effects must be explicit writes");
            if (left->memoryLocation() == convention.volatileLocation) {
                volatileWrite = index;
            } else if (left->memoryLocation() == convention.returnLocation) {
                returnWrite = index;
            }
            check(assignment->right()->is<Intrinsic>() &&
                      assignment->right()->asIntrinsic()->intrinsicKind() ==
                          Intrinsic::UNDEFINED,
                  "call-clobbered registers must receive undefined values");
        }
        ++index;
    }

    check(volatileWrite != (std::numeric_limits<std::size_t>::max)(),
          "a convention's caller-saved register must be killed at calls");
    check(returnWrite != (std::numeric_limits<std::size_t>::max)(),
          "an unknown signature must still model candidate return registers");
    check(volatileWrite < returnWrite,
          "the return definition must follow the general caller-saved kill");
}

struct StackCleanupEffect {
    bool isExactStackOffset;
    bool mayBeStackOffset;
    SignedConstantValue stackOffset;
};

StackCleanupEffect analyzeStackCleanupEffect(
        bool calleeCleanup,
        const boost::optional<ByteSize> &stackArgumentsSize,
        const boost::optional<ByteSize> &exactReturnCleanup) {
    const ConstantValue targetAddress = 0x7a00;
    TestArchitecture architecture;
    TestStackConvention convention(calleeCleanup);

    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    std::unique_ptr<Call> call(new Call(constant(32, targetAddress)));
    block->pushBack(std::move(call));

    std::unique_ptr<Term> stackRead(
        new MemoryLocationAccess(convention.stackPointerLocation));
    Term *stackReadTerm = stackRead.get();
    block->pushBack(std::unique_ptr<Statement>(
        new Touch(std::move(stackRead), Term::READ)));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    const calling::CalleeId targetId{
        calling::EntryAddress(targetAddress)};
    calling::Conventions conventions;
    conventions.setConvention(calling::CalleeId(&function), &convention);
    conventions.setConvention(targetId, &convention);
    conventions.setStackArgumentsSize(targetId, stackArgumentsSize);
    if (exactReturnCleanup) {
        conventions.setReturnStackCleanupSize(
            targetId, *exactReturnCleanup);
    }

    calling::Signatures signatures;
    calling::Hooks hooks(conventions, signatures);
    Dataflow dataflow;
    hooks.instrument(&function, &dataflow);

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(
        dataflow, &architecture, canceled, log).analyze(cfg);
    check(dataflow.converged(),
          "the stack-cleanup fixture must reach a dataflow fixpoint");

    const Value *value = dataflow.findValue(stackReadTerm);
    check(value != nullptr,
          "the post-call stack-pointer read must be analyzed");
    return StackCleanupEffect{
        value->isStackOffset(), value->mayBeStackOffset(),
        value->isStackOffset() ? value->stackOffset() : 0};
}

void testCallStackCleanupSoundness() {
    const StackCleanupEffect unknownCalleeCleanup =
        analyzeStackCleanupEffect(true, boost::none, boost::none);
    check(!unknownCalleeCleanup.isExactStackOffset &&
              unknownCalleeCleanup.mayBeStackOffset,
          "callee cleanup with unknown extent must make the post-call SP undefined");

    const StackCleanupEffect callerCleanup =
        analyzeStackCleanupEffect(false, boost::none, boost::none);
    check(callerCleanup.isExactStackOffset &&
              callerCleanup.stackOffset == 0,
          "caller-cleanup ABI must preserve SP when no immediate cleanup is known");

    const StackCleanupEffect knownCalleeCleanup =
        analyzeStackCleanupEffect(true, ByteSize(8), boost::none);
    check(knownCalleeCleanup.isExactStackOffset &&
              knownCalleeCleanup.stackOffset == 8,
          "known callee-cleanup extent must advance SP exactly");

    const StackCleanupEffect exactReturnCleanup =
        analyzeStackCleanupEffect(true, ByteSize(4), ByteSize(12));
    check(exactReturnCleanup.isExactStackOffset &&
              exactReturnCleanup.stackOffset == 12,
          "exact return cleanup must override an argument-size estimate");
}

void testResolvedTargetOverridesCallSiteFallback() {
    const ConstantValue targetAddress = 0x7900;

    auto analyze = [&](bool authoritativeCallSite) {
        TestArchitecture architecture;
        TestConvention targetConvention;
        TestStackConvention callSiteConvention;
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        TestInstruction callInstruction(0x1200, 5);

        std::unique_ptr<Call> callStorage(new Call(
            constant(32, targetAddress)));
        Call *call = callStorage.get();
        callStorage->setInstruction(&callInstruction);
        block->pushBack(std::move(callStorage));
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const calling::CalleeId callSiteId(
            calling::CallAddress(callInstruction.addr()));
        calling::Conventions conventions;
        conventions.setConvention(
            calling::CalleeId(&function), &targetConvention);
        conventions.setConvention(
            calling::CalleeId(
                calling::EntryAddress(targetAddress)),
            &targetConvention);
        if (authoritativeCallSite) {
            conventions.setConvention(
                callSiteId, &callSiteConvention);
        } else {
            conventions.setFallbackConvention(
                callSiteId, &callSiteConvention);
            check(conventions.isFallbackConvention(callSiteId),
                  "an unresolved call-site default must retain fallback provenance");
        }

        calling::Signatures signatures;
        calling::Hooks hooks(conventions, signatures);
        Dataflow dataflow;
        hooks.instrument(&function, &dataflow);
        CFG cfg(function.basicBlocks());
        CancellationToken canceled;
        LogToken log;
        DataflowAnalyzer(
            dataflow, &architecture, canceled, log).analyze(cfg);
        check(dataflow.converged(),
              "the call-site provenance fixture must converge");

        const calling::CallHook *hook = hooks.getCallHook(call);
        check(hook && hook->stackPointer(),
              "the resolved call must install a stack-aware hook");
        return dataflow.getMemoryLocation(hook->stackPointer());
    };

    check(analyze(false) == TestConvention().stackPointer(),
          "a resolved target convention must override an unresolved call-site fallback");
    check(analyze(true) == TestStackConvention().stackPointerLocation,
          "authoritative call-site metadata must override the resolved target");

    calling::Conventions conventions;
    TestConvention fallback;
    TestStackConvention authoritative;
    const calling::CalleeId id(calling::CallAddress(0x1234));
    conventions.setFallbackConvention(id, &fallback);
    conventions.setConvention(id, &authoritative);
    conventions.setFallbackConvention(id, &fallback);
    check(conventions.getConvention(id) == &authoritative &&
              !conventions.isFallbackConvention(id),
          "strong convention evidence must clear and resist later fallback defaults");
}

enum CallContractKind {
    EXACT_CALL_CONTRACT,
    DEFAULT_INCOMPLETE_PROTOTYPE,
    INFERRED_CALL_CONTRACT,
    MISMATCHED_CALL_CONTRACT,
    NO_CALL_SIGNATURE
};

struct CallEffectResult {
    bool stackStoreLive;
    bool otherMemoryStoreLive;
    bool stackStoreMustBeMaterialized;
    bool otherMemoryStoreMustBeMaterialized;
    bool postCallReadIsConcrete;
    bool postCallReadHasUnknownDefinition;
    bool postOtherMemoryReadIsConcrete;
    bool postOtherMemoryReadHasUnknownDefinition;
};

CallEffectResult analyzeCallEffect(bool passStackAddress,
                                   bool mayReadMemory,
                                   bool mayWriteMemory,
                                   CallContractKind contractKind =
                                       EXACT_CALL_CONTRACT,
                                   bool readStackAfterCall = false,
                                   bool readOtherMemoryAfterCall = false) {
    const ConstantValue targetAddress = 0x7000;
    const MemoryLocation stackSlot(MemoryDomain::STACK, -128, 32);
    const MemoryLocation otherMemorySlot(
        MemoryDomain::USER, 0x1234 * CHAR_BIT, 32);
    const MemoryLocation argumentLocation(
        MemoryDomain::FIRST_REGISTER + 43, 0, 32);

    TestArchitecture architecture;
    TestConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    Term *stackDefinition = addDefinition(
        block, stackSlot, constant(32, 0x12345678));
    Term *otherMemoryDefinition = addDefinition(
        block, otherMemorySlot, constant(32, 0x87654321));
    addDefinition(
        block, argumentLocation,
        passStackAddress ?
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::ZERO_STACK_OFFSET, 32)) :
            constant(32, 0x1234));

    std::unique_ptr<Call> callStorage(new Call(
        constant(32, targetAddress)));
    Call *call = callStorage.get();
    block->pushBack(std::move(callStorage));

    Term *postCallRead = nullptr;
    if (readStackAfterCall) {
        const MemoryLocation postCallResult(
            MemoryDomain::MEMORY, 0x9000, 32);
        std::unique_ptr<Term> postCallReadStorage(
            new MemoryLocationAccess(stackSlot));
        postCallRead = postCallReadStorage.get();
        addDefinition(block, postCallResult, std::move(postCallReadStorage));
    }
    Term *postOtherMemoryRead = nullptr;
    if (readOtherMemoryAfterCall) {
        const MemoryLocation postCallResult(
            MemoryDomain::MEMORY, 0xa000, 32);
        std::unique_ptr<Term> postCallReadStorage(
            new MemoryLocationAccess(otherMemorySlot));
        postOtherMemoryRead = postCallReadStorage.get();
        addDefinition(block, postCallResult, std::move(postCallReadStorage));
    }
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    std::shared_ptr<calling::CallSignature> signature(
        new calling::CallSignature());
    signature->arguments().push_back(std::shared_ptr<const Term>(
        new MemoryLocationAccess(argumentLocation)));
    if (contractKind == EXACT_CALL_CONTRACT ||
        contractKind == DEFAULT_INCOMPLETE_PROTOTYPE)
    {
        std::vector<calling::ParameterDescription> parameters;
        const calling::ParameterDescription::PointeeAccess pointeeAccess =
            mayReadMemory ?
                (mayWriteMemory ?
                    calling::ParameterDescription::PointeeAccess::READ_WRITE :
                    calling::ParameterDescription::PointeeAccess::READ) :
                (mayWriteMemory ?
                    calling::ParameterDescription::PointeeAccess::WRITE :
                    calling::ParameterDescription::PointeeAccess::NONE);
        parameters.push_back(calling::ParameterDescription(
            QString(),
            calling::TypeDescription(
                calling::TypeDescription::POINTER, 32, true),
            pointeeAccess));
        signature->setPrototype(
            std::shared_ptr<const calling::FunctionPrototype>(
                new calling::FunctionPrototype(
                    calling::TypeDescription(
                        calling::TypeDescription::VOID, 0, false),
                    parameters, QString(), QString(),
                    contractKind == EXACT_CALL_CONTRACT)));
    } else if (contractKind == MISMATCHED_CALL_CONTRACT) {
        signature->setPrototype(
            std::shared_ptr<const calling::FunctionPrototype>(
                new calling::FunctionPrototype(
                    calling::TypeDescription(
                        calling::TypeDescription::VOID, 0, false),
                    std::vector<calling::ParameterDescription>(),
                    QString(), QString(), true)));
    }

    calling::Conventions conventions;
    conventions.setConvention(calling::CalleeId(&function), &convention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(targetAddress)),
        &convention);

    calling::Signatures signatures;
    if (contractKind != NO_CALL_SIGNATURE) {
        signatures.setSignature(
            call, signature,
            contractKind == INFERRED_CALL_CONTRACT ?
                calling::SignatureSource::INFERRED :
                calling::SignatureSource::EXTERNAL);
    }

    Dataflow dataflow;
    calling::Hooks hooks(conventions, signatures);
    hooks.instrument(&function, &dataflow);

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);
    check(dataflow.converged(),
          "the call-pointee regression fixture must reach a dataflow fixpoint");

    const calling::CallHook *callHook = hooks.getCallHook(call);
    check(callHook != nullptr,
          "a call must have a call hook after dataflow analysis");
    check((callHook->snapshotStatement() != nullptr) ==
              (contractKind == NO_CALL_SIGNATURE ||
               contractKind == INFERRED_CALL_CONTRACT),
          "only an unknown or inferred call must use the inference snapshot");
    const bool needsPointeeSnapshot =
        contractKind != NO_CALL_SIGNATURE &&
        (contractKind != EXACT_CALL_CONTRACT || mayReadMemory);
    check((callHook->pointeeReadSnapshotStatement() != nullptr) ==
              needsPointeeSnapshot,
          "the pre-effect snapshot must follow contract completeness and read effects");

    bool snapshotContainsStackDefinition = false;
    bool snapshotContainsOtherMemoryDefinition = false;
    const Statement *effectSnapshot =
        contractKind == NO_CALL_SIGNATURE ?
            callHook->snapshotStatement() :
            callHook->pointeeReadSnapshotStatement();
    if (effectSnapshot) {
        foreach (const auto &chunk,
                 dataflow.getDefinitions(effectSnapshot).chunks()) {
            if (chunk.location().domain() == MemoryDomain::STACK) {
                foreach (const Term *definition, chunk.definitions()) {
                    if (definition == stackDefinition) {
                        snapshotContainsStackDefinition = true;
                    }
                }
            }
            foreach (const Term *definition, chunk.definitions()) {
                if (definition == otherMemoryDefinition) {
                    snapshotContainsOtherMemoryDefinition = true;
                }
            }
        }
    }
    const bool mustSnapshotMemory =
        contractKind != EXACT_CALL_CONTRACT || mayReadMemory;
    check(snapshotContainsStackDefinition == mustSnapshotMemory,
          "a pre-effect snapshot must capture every conservatively readable stack definition");
    check(snapshotContainsOtherMemoryDefinition == mustSnapshotMemory,
          "a pre-effect snapshot must capture every conservatively readable non-stack definition");

    if (contractKind != NO_CALL_SIGNATURE) {
        const Term *argumentTerm = callHook->getArgumentTerm(
            signature->arguments().front().get());
        check(argumentTerm != nullptr,
              "a call hook must retain the actual argument read term");
        const Value *argumentValue = dataflow.findValue(argumentTerm);
        check(argumentValue != nullptr,
              "dataflow must classify every instrumented call argument");
        check(argumentValue->mayBeStackOffset() == passStackAddress,
              "the fixture must distinguish stack-derived and definite non-stack arguments");
    }

    bool postCallReadIsConcrete = false;
    bool postCallReadHasUnknownDefinition = false;
    if (postCallRead) {
        foreach (const auto &chunk,
                 dataflow.getDefinitions(postCallRead).chunks()) {
            postCallReadHasUnknownDefinition =
                postCallReadHasUnknownDefinition ||
                chunk.hasUnknownDefinition();
        }
        const Value *postCallValue = dataflow.findValue(postCallRead);
        check(postCallValue != nullptr,
              "dataflow must evaluate the stack read after the call");
        postCallReadIsConcrete =
            postCallValue->abstractValue().isConcrete();
    }

    bool postOtherMemoryReadIsConcrete = false;
    bool postOtherMemoryReadHasUnknownDefinition = false;
    if (postOtherMemoryRead) {
        foreach (const auto &chunk,
                 dataflow.getDefinitions(postOtherMemoryRead).chunks()) {
            postOtherMemoryReadHasUnknownDefinition =
                postOtherMemoryReadHasUnknownDefinition ||
                chunk.hasUnknownDefinition();
        }
        const Value *postCallValue =
            dataflow.findValue(postOtherMemoryRead);
        check(postCallValue != nullptr,
              "dataflow must evaluate the non-stack memory read after the call");
        postOtherMemoryReadIsConcrete =
            postCallValue->abstractValue().isConcrete();
    }

    liveness::Liveness liveness;
    liveness::LivenessAnalyzer(
        liveness, &function, dataflow, &architecture, nullptr,
        hooks, &signatures, log).analyze();
    return CallEffectResult{
        liveness.isLive(stackDefinition),
        liveness.isLive(otherMemoryDefinition),
        liveness.mustBeMaterialized(stackDefinition),
        liveness.mustBeMaterialized(otherMemoryDefinition),
        postCallReadIsConcrete,
        postCallReadHasUnknownDefinition,
        postOtherMemoryReadIsConcrete,
        postOtherMemoryReadHasUnknownDefinition
    };
}

void testCallPointeeReadLiveness() {
    const CallEffectResult stackRead =
        analyzeCallEffect(true, true, false);
    check(stackRead.stackStoreLive && !stackRead.otherMemoryStoreLive,
          "a stack-address call argument must keep pre-call stack stores live");
    check(stackRead.stackStoreMustBeMaterialized &&
              !stackRead.otherMemoryStoreMustBeMaterialized,
          "a call snapshot must materialize exactly the stack definition it observes");
    const CallEffectResult otherMemoryRead =
        analyzeCallEffect(false, true, false);
    check(!otherMemoryRead.stackStoreLive &&
              otherMemoryRead.otherMemoryStoreLive,
          "a definite non-stack call argument must preserve only non-register memory it may read");
    check(!otherMemoryRead.stackStoreMustBeMaterialized &&
              otherMemoryRead.otherMemoryStoreMustBeMaterialized,
          "a call snapshot must materialize exactly the non-stack definition it observes");
    check(!analyzeCallEffect(true, false, true).stackStoreLive,
          "a call's write-only effect alone must not keep its incoming value live");
    check(analyzeCallEffect(true, true, true).stackStoreLive,
          "a read-write stack pointee must preserve its incoming value");
    const CallEffectResult defaultIncomplete = analyzeCallEffect(
        false, false, false, DEFAULT_INCOMPLETE_PROTOTYPE);
    check(defaultIncomplete.stackStoreLive &&
              defaultIncomplete.otherMemoryStoreLive,
          "a prototype without complete effects must preserve every memory definition the callee may read");
    check(defaultIncomplete.stackStoreMustBeMaterialized &&
              defaultIncomplete.otherMemoryStoreMustBeMaterialized,
          "an incomplete contract's snapshot must materialize every memory definition it may observe");
}

void testCallPointeeWriteInvalidation() {
    const CallEffectResult stackWrite =
        analyzeCallEffect(
            true, false, true, EXACT_CALL_CONTRACT, true, true);
    check(stackWrite.stackStoreLive &&
              !stackWrite.postCallReadIsConcrete &&
              stackWrite.postCallReadHasUnknownDefinition &&
              stackWrite.postOtherMemoryReadIsConcrete &&
              !stackWrite.postOtherMemoryReadHasUnknownDefinition,
          "an exact stack output must invalidate frame state without clobbering other memory");

    const CallEffectResult stackReadWrite =
        analyzeCallEffect(
            true, true, true, EXACT_CALL_CONTRACT, true, true);
    check(stackReadWrite.stackStoreLive &&
              !stackReadWrite.postCallReadIsConcrete &&
              stackReadWrite.postCallReadHasUnknownDefinition,
          "a read-write stack pointer must preserve input liveness and invalidate its old value");

    const CallEffectResult nonStackWrite =
        analyzeCallEffect(
            false, false, true, EXACT_CALL_CONTRACT, true, true);
    check(nonStackWrite.postCallReadIsConcrete &&
              !nonStackWrite.postCallReadHasUnknownDefinition &&
              !nonStackWrite.postOtherMemoryReadIsConcrete &&
              nonStackWrite.postOtherMemoryReadHasUnknownDefinition,
          "an exact non-stack output must preserve frame facts and invalidate tracked non-register memory");

    const CallEffectResult inferredCall = analyzeCallEffect(
        false, false, false, INFERRED_CALL_CONTRACT, true, true);
    check(inferredCall.stackStoreLive &&
              !inferredCall.postCallReadIsConcrete &&
              inferredCall.postCallReadHasUnknownDefinition &&
              inferredCall.otherMemoryStoreLive &&
              !inferredCall.postOtherMemoryReadIsConcrete &&
              inferredCall.postOtherMemoryReadHasUnknownDefinition,
          "an inferred contract must conservatively read and clobber all tracked non-register memory");

    const CallEffectResult defaultIncompletePrototype = analyzeCallEffect(
        false, false, false, DEFAULT_INCOMPLETE_PROTOTYPE, true, true);
    check(defaultIncompletePrototype.stackStoreLive &&
              !defaultIncompletePrototype.postCallReadIsConcrete &&
              defaultIncompletePrototype.postCallReadHasUnknownDefinition &&
              !defaultIncompletePrototype.postOtherMemoryReadIsConcrete &&
              defaultIncompletePrototype.postOtherMemoryReadHasUnknownDefinition,
          "a prototype without an explicit complete-effect promise must use the conservative fallback");

    const CallEffectResult unknownCall = analyzeCallEffect(
        false, false, false, NO_CALL_SIGNATURE, true, true);
    check(unknownCall.stackStoreLive &&
              !unknownCall.postCallReadIsConcrete &&
              unknownCall.postCallReadHasUnknownDefinition &&
              !unknownCall.postOtherMemoryReadIsConcrete &&
              unknownCall.postOtherMemoryReadHasUnknownDefinition,
          "a call without a signature must conservatively read and clobber all tracked memory");

    const CallEffectResult mismatchedCall = analyzeCallEffect(
        false, false, false, MISMATCHED_CALL_CONTRACT, true, true);
    check(mismatchedCall.stackStoreLive &&
              !mismatchedCall.postCallReadIsConcrete &&
              mismatchedCall.postCallReadHasUnknownDefinition &&
              !mismatchedCall.postOtherMemoryReadIsConcrete &&
              mismatchedCall.postOtherMemoryReadHasUnknownDefinition,
          "a parameter-count mismatch must use the conservative incomplete-contract fallback");
}

void testCallSnapshotDoesNotMaterializeControlReturnAddress() {
    const ConstantValue targetAddress = 0x7100;
    const MemoryLocation returnAddressSlot(
        MemoryDomain::STACK, -32, 32);
    const MemoryLocation sourceStackSlot(
        MemoryDomain::STACK, -64, 32);

    TestArchitecture architecture;
    TestConvention convention;
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    std::unique_ptr<Term> returnAddressDestination(
        new MemoryLocationAccess(returnAddressSlot));
    Term *returnAddressDefinition = returnAddressDestination.get();
    block->pushBack(std::unique_ptr<Statement>(new Assignment(
        std::move(returnAddressDestination),
        constant(32, 0x401005),
        Assignment::CONTROL_FLOW_STATE)));
    Term *sourceStackDefinition = addDefinition(
        block, sourceStackSlot, constant(32, 0x12345678));
    std::unique_ptr<Call> callStorage(new Call(
        constant(32, targetAddress)));
    Call *call = callStorage.get();
    block->pushBack(std::move(callStorage));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    calling::Conventions conventions;
    conventions.setConvention(calling::CalleeId(&function), &convention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(targetAddress)),
        &convention);
    calling::Signatures signatures;
    Dataflow dataflow;
    calling::Hooks hooks(conventions, signatures);
    hooks.instrument(&function, &dataflow);

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);
    check(dataflow.converged(),
          "the control-stack liveness fixture must converge");
    check(hooks.getCallHook(call) != nullptr &&
              hooks.getCallHook(call)->snapshotStatement() != nullptr,
          "an unknown call must retain its conservative snapshot");
    liveness::Liveness liveness;
    liveness::LivenessAnalyzer(
        liveness, &function, dataflow, &architecture, nullptr,
        hooks, &signatures, log).analyze();

    check(!liveness.isLive(returnAddressDefinition) &&
              !liveness.mustBeMaterialized(returnAddressDefinition),
          "a call snapshot must not expose synthetic CALL/RET state as source memory");
    check(liveness.isLive(sourceStackDefinition) &&
              liveness.mustBeMaterialized(sourceStackDefinition),
          "excluding control state must preserve conservative source-memory observations");
}

void testDominanceAndPostDominance() {
    Function function;
    BasicBlock *entry = addBlock(function);
    BasicBlock *left = addBlock(function);
    BasicBlock *right = addBlock(function);
    BasicBlock *join = addBlock(function);
    BasicBlock *closedLoop = addBlock(function);
    function.setEntry(entry);

    entry->pushBack(std::unique_ptr<Statement>(new Jump(
        constant(1, 1), JumpTarget(left), JumpTarget(right))));
    left->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(join))));
    right->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(join))));
    join->pushBack(std::unique_ptr<Statement>(new Halt()));
    closedLoop->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(closedLoop))));

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    Dominators dominators(cfg, canceled, entry);
    PostDominators postdominators(cfg, canceled);

    check(dominators.isDominating(entry, left),
          "entry must dominate its reachable branch");
    check(dominators.isDominating(entry, join),
          "entry must dominate the diamond join");
    check(!dominators.isDominating(left, join),
          "one diamond arm must not dominate the join");
    check(!dominators.isDominating(entry, closedLoop),
          "entry must not dominate a detached component");
    check(dominators.isDominating(closedLoop, closedLoop),
          "a detached block must conservatively dominate only itself");

    check(postdominators.canReachExit(entry),
          "diamond entry must reach a real exit");
    check(postdominators.isPostDominating(join, entry),
          "the diamond join must postdominate its entry");
    check(postdominators.getImmediatePostDominator(entry) == join,
          "diamond entry must have the join as immediate postdominator");
    std::vector<const BasicBlock *> branches;
    branches.push_back(left);
    branches.push_back(right);
    check(postdominators.getNearestCommonPostDominator(branches) == join,
          "diamond arms must have the join as nearest common postdominator");
    check(!postdominators.canReachExit(closedLoop),
          "a closed loop must not manufacture an exit path");
    check(postdominators.getImmediatePostDominator(closedLoop) == nullptr,
          "an exit-unreachable loop must not have an immediate postdominator");
}

void testAlternativeReachingDefinitions() {
    const MemoryLocation valueLocation(
        MemoryDomain::FIRST_REGISTER + 50, 0, 32);
    const MemoryLocation sinkLocation(
        MemoryDomain::FIRST_REGISTER + 51, 0, 32);

    /* One branch defines the value and the other preserves the value which
     * entered the function. The latter must not disappear at the join. */
    {
        Function function;
        BasicBlock *entry = addBlock(function);
        BasicBlock *left = addBlock(function);
        BasicBlock *right = addBlock(function);
        BasicBlock *join = addBlock(function);
        function.setEntry(entry);

        entry->pushBack(std::unique_ptr<Statement>(new Jump(
            constant(1, 1), JumpTarget(left), JumpTarget(right))));
        Term *leftDefinition = addDefinition(
            left, valueLocation, constant(32, 7));
        left->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        right->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        ReadDefinition read = addReadDefinition(
            join, valueLocation, sinkLocation);
        join->pushBack(std::unique_ptr<Statement>(new Halt()));

        TestArchitecture architecture;
        CancellationToken canceled;
        LogToken log;
        Dataflow dataflow;
        CFG cfg(function.basicBlocks());
        DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);

        check(dataflow.converged(),
              "a finite diamond must reach a dataflow fixpoint");
        const ReachingDefinitions &definitions =
            dataflow.getDefinitions(read.read);
        check(definitions.chunks().size() == 1,
              "the diamond read must retain one exact range");
        const ReachingDefinitions::Chunk &chunk =
            definitions.chunks().front();
        check(chunk.location() == valueLocation &&
                  chunk.hasIncomingDefinition() &&
                  !chunk.hasUnknownDefinition() &&
                  chunk.definitions().size() == 1 &&
                  chunk.definitions().front() == leftDefinition,
              "a one-sided branch definition must retain the incoming alternative");
        const Value *value = dataflow.findValue(read.read);
        check(value != nullptr && !value->abstractValue().isConcrete(),
              "an incoming CFG alternative must block stale constant propagation");

        DefUseGraph defUse(dataflow);
        check(defUse.definitions(read.read).hasIncomingDefinition() &&
                  !defUse.definitions(read.read).isComplete() &&
                  defUse.uniqueDefinition(read.read) == nullptr,
              "def-use queries must expose path-incomplete incoming values");
    }

    /* Distinct definitions on every alternative are path-complete. Their
     * abstract values may still meet to the same constant. */
    {
        Function function;
        BasicBlock *entry = addBlock(function);
        BasicBlock *left = addBlock(function);
        BasicBlock *right = addBlock(function);
        BasicBlock *join = addBlock(function);
        function.setEntry(entry);

        entry->pushBack(std::unique_ptr<Statement>(new Jump(
            constant(1, 1), JumpTarget(left), JumpTarget(right))));
        addDefinition(left, valueLocation, constant(32, 7));
        left->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        addDefinition(right, valueLocation, constant(32, 7));
        right->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        ReadDefinition read = addReadDefinition(
            join, valueLocation, sinkLocation);
        join->pushBack(std::unique_ptr<Statement>(new Halt()));

        TestArchitecture architecture;
        CancellationToken canceled;
        LogToken log;
        Dataflow dataflow;
        CFG cfg(function.basicBlocks());
        DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);

        const ReachingDefinitions &definitions =
            dataflow.getDefinitions(read.read);
        check(definitions.chunks().size() == 1 &&
                  !definitions.chunks().front().hasIncomingDefinition() &&
                  definitions.chunks().front().definitions().size() == 2,
              "definitions present on both diamond arms must be path-complete");
        const Value *value = dataflow.findValue(read.read);
        check(value != nullptr && value->abstractValue().isConcrete() &&
                  value->abstractValue().asConcrete().value() == 7,
              "equal constants from complete alternatives must remain concrete");

        DefUseGraph defUse(dataflow);
        check(defUse.definitions(read.read).isComplete() &&
                  defUse.uniqueDefinition(read.read) == nullptr,
              "a complete multi-definition read must not claim a unique definition");
    }

    /* Partial overlap is split at exact bit boundaries: only the upper half
     * is absent on the path which writes the low half. */
    {
        const MemoryLocation lowHalf(
            valueLocation.domain(), valueLocation.addr(), 16);
        const MemoryLocation highHalf(
            valueLocation.domain(), valueLocation.addr() + 16, 16);

        Function function;
        BasicBlock *entry = addBlock(function);
        BasicBlock *left = addBlock(function);
        BasicBlock *right = addBlock(function);
        BasicBlock *join = addBlock(function);
        function.setEntry(entry);

        entry->pushBack(std::unique_ptr<Statement>(new Jump(
            constant(1, 1), JumpTarget(left), JumpTarget(right))));
        addDefinition(left, valueLocation, constant(32, 0x12345678));
        left->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        addDefinition(right, lowHalf, constant(16, 0x5678));
        right->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        ReadDefinition read = addReadDefinition(
            join, valueLocation, sinkLocation);
        join->pushBack(std::unique_ptr<Statement>(new Halt()));

        TestArchitecture architecture;
        CancellationToken canceled;
        LogToken log;
        Dataflow dataflow;
        CFG cfg(function.basicBlocks());
        DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);

        const ReachingDefinitions &definitions =
            dataflow.getDefinitions(read.read);
        const ReachingDefinitions::Chunk *low =
            findChunk(definitions, lowHalf);
        const ReachingDefinitions::Chunk *high =
            findChunk(definitions, highHalf);
        check(low != nullptr && !low->hasIncomingDefinition() &&
                  low->definitions().size() == 2,
              "overlapping subranges must combine both path definitions");
        check(high != nullptr && high->hasIncomingDefinition() &&
                  high->definitions().size() == 1,
              "only a one-sided suffix may carry the incoming marker");
        const Value *value = dataflow.findValue(read.read);
        check(value != nullptr && !value->abstractValue().isConcrete(),
              "a partially incoming value must not be folded to a constant");
    }

    /* A range absent on every path has no chunk to annotate at the CFG join.
     * The value lattice must still model those uncovered bits as incoming. */
    {
        const MemoryLocation lowHalf(
            valueLocation.domain(), valueLocation.addr(), 16);
        Function function;
        BasicBlock *entry = addBlock(function);
        function.setEntry(entry);
        addDefinition(entry, lowHalf, constant(16, 0x5678));
        ReadDefinition read = addReadDefinition(
            entry, valueLocation, sinkLocation);
        entry->pushBack(std::unique_ptr<Statement>(new Halt()));

        TestArchitecture architecture;
        CancellationToken canceled;
        LogToken log;
        Dataflow dataflow;
        CFG cfg(function.basicBlocks());
        DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);

        const Value *value = dataflow.findValue(read.read);
        const ConstantValue highMask = ConstantValue(0xffff) << 16;
        check(value != nullptr &&
                  (value->abstractValue().zeroBits() & highMask) == highMask &&
                  (value->abstractValue().oneBits() & highMask) == highMask,
              "bits absent from every reaching-definition chunk must be abstract top");
        DefUseGraph defUse(dataflow);
        check(!defUse.definitions(read.read).coversWholeLocation() &&
                  !defUse.definitions(read.read).isComplete(),
              "an uncovered read range must remain incomplete in def-use data");
    }

    /* A back edge into the function entry is joined with the implicit caller
     * edge. The first iteration therefore retains an incoming value. */
    {
        Function function;
        BasicBlock *entry = addBlock(function);
        BasicBlock *body = addBlock(function);
        BasicBlock *exit = addBlock(function);
        function.setEntry(entry);

        ReadDefinition read = addReadDefinition(
            entry, valueLocation, sinkLocation);
        entry->pushBack(std::unique_ptr<Statement>(new Jump(
            constant(1, 1), JumpTarget(body), JumpTarget(exit))));
        Term *backEdgeDefinition = addDefinition(
            body, valueLocation, constant(32, 9));
        body->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(entry))));
        exit->pushBack(std::unique_ptr<Statement>(new Halt()));

        TestArchitecture architecture;
        CancellationToken canceled;
        LogToken log;
        Dataflow dataflow;
        CFG cfg(function.basicBlocks());
        DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(cfg);

        const ReachingDefinitions &definitions =
            dataflow.getDefinitions(read.read);
        check(definitions.chunks().size() == 1 &&
                  definitions.chunks().front().hasIncomingDefinition() &&
                  definitions.chunks().front().definitions().size() == 1 &&
                  definitions.chunks().front().definitions().front() ==
                      backEdgeDefinition,
              "an entry back edge must not erase the caller-provided value");
    }
}

void testOpaqueMayWriteInvalidation() {
    const MemoryLocation lowStack(
        MemoryDomain::STACK,
        (std::numeric_limits<BitAddr>::min)() + 64, 32);
    const MemoryLocation highStack(
        MemoryDomain::STACK,
        (std::numeric_limits<BitAddr>::max)() - 96, 32);
    const MemoryLocation registerLocation(
        MemoryDomain::FIRST_REGISTER + 52, 0, 32);

    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);
    Term *lowDefinition = addDefinition(
        block, lowStack, constant(32, 1));
    Term *highDefinition = addDefinition(
        block, highStack, constant(32, 2));
    Term *registerDefinition = addDefinition(
        block, registerLocation, constant(32, 3));

    TestArchitecture architecture;
    CancellationToken canceled;
    LogToken log;

    {
        ReachingDefinitions definitions;
        definitions.addDefinition(lowStack, lowDefinition);
        definitions.addDefinition(highStack, highDefinition);
        std::vector<std::unique_ptr<Term>> candidates;
        candidates.push_back(std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::ZERO_STACK_OFFSET, 64)));
        TrackedMemoryInvalidation invalidation(std::move(candidates));
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&invalidation, definitions);

        const ReachingDefinitions::Chunk *low =
            findChunk(definitions, lowStack);
        const ReachingDefinitions::Chunk *high =
            findChunk(definitions, highStack);
        check(definitions.chunks().size() == 2 && low && high &&
                  low->hasUnknownDefinition() &&
                  high->hasUnknownDefinition(),
              "stack invalidation must preserve disjoint tracked intervals without a bounding gap");
    }

    {
        ReachingDefinitions definitions;
        definitions.addDefinition(lowStack, lowDefinition);
        definitions.addDefinition(registerLocation, registerDefinition);
        InlineAssembly assembly;
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&assembly, definitions);

        const ReachingDefinitions::Chunk *stackChunk =
            findChunk(definitions, lowStack);
        const ReachingDefinitions::Chunk *registerChunk =
            findChunk(definitions, registerLocation);
        check(stackChunk && registerChunk &&
                  stackChunk->hasUnknownDefinition() &&
                  registerChunk->hasUnknownDefinition(),
              "opaque inline assembly must contaminate every tracked interval");
    }

    {
        ReachingDefinitions definitions;
        definitions.addDefinition(lowStack, lowDefinition);
        Assignment unresolvedWrite(
            std::unique_ptr<Term>(new Dereference(
                std::unique_ptr<Term>(new Intrinsic(
                    Intrinsic::UNKNOWN, 64)),
                MemoryDomain::MEMORY, 32)),
            constant(32, 4));
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&unresolvedWrite, definitions);

        const ReachingDefinitions::Chunk *chunk =
            findChunk(definitions, lowStack);
        check(chunk && chunk->hasUnknownDefinition(),
              "an unresolved possibly stack-derived write must contaminate tracked frame storage");

        const MemoryLocation unseenCustomMemory(
            MemoryDomain::USER + 8, 0x2c0, 32);
        std::unique_ptr<Term> readStorage(
            new MemoryLocationAccess(unseenCustomMemory));
        Term *read = readStorage.get();
        Touch readStatement(std::move(readStorage), Term::READ);
        analyzer.execute(&readStatement, definitions);
        const ReachingDefinitions &readDefinitions =
            dataflow.getDefinitions(read);
        const ReachingDefinitions::Chunk *readChunk =
            findChunk(readDefinitions, unseenCustomMemory);
        check(readDefinitions.chunks().size() == 1 && readChunk &&
                  readChunk->hasUnknownDefinition() &&
                  readChunk->hasIncomingDefinition() &&
                  readChunk->definitions().empty(),
              "a fully unresolved indirect write must preserve and contaminate newly observed non-stack memory");
    }

    {
        Assignment recurringWrite(
            std::unique_ptr<Term>(new Dereference(
                std::unique_ptr<Term>(new Intrinsic(
                    Intrinsic::UNKNOWN, 64)),
                MemoryDomain::MEMORY, 32)),
            constant(32, 6));
        ReachingDefinitions definitions;
        definitions.addDefinition(lowStack, recurringWrite.left());
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&recurringWrite, definitions);

        const ReachingDefinitions observedDefinitions =
            definitions.projected(lowStack);
        const ReachingDefinitions::Chunk *chunk =
            findChunk(observedDefinitions, lowStack);
        check(chunk && chunk->hasUnknownDefinition(),
              "an unresolved recurring write must retain and contaminate its previously resolved range");
    }

    {
        ReachingDefinitions definitions;
        definitions.addDefinition(lowStack, lowDefinition);
        Assignment nonStackWrite(
            std::unique_ptr<Term>(new Dereference(
                std::unique_ptr<Term>(new Intrinsic(
                    Intrinsic::RETURN_ADDRESS, 64)),
                MemoryDomain::MEMORY, 32)),
            constant(32, 5));
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&nonStackWrite, definitions);

        const ReachingDefinitions::Chunk *chunk =
            findChunk(definitions, lowStack);
        check(chunk && !chunk->hasUnknownDefinition() &&
                  chunk->definitions().size() == 1 &&
                  chunk->definitions().front() == lowDefinition,
              "an unresolved definite non-stack write must preserve frame definitions");
    }

    /* An extent-less may-write through an exact frame pointer applies to
     * stack storage first observed after the call, while preserving the
     * pre-call entry value as the alternative where no write occurred. */
    {
        const MemoryLocation unseenStack(
            MemoryDomain::STACK, 0, 32);
        ReachingDefinitions definitions;
        std::vector<std::unique_ptr<Term>> candidates;
        candidates.push_back(std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::ZERO_STACK_OFFSET, 64)));
        TrackedMemoryInvalidation invalidation(std::move(candidates));
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&invalidation, definitions);

        std::unique_ptr<Term> readStorage(
            new MemoryLocationAccess(unseenStack));
        Term *read = readStorage.get();
        Touch readStatement(std::move(readStorage), Term::READ);
        analyzer.execute(&readStatement, definitions);

        const ReachingDefinitions &readDefinitions =
            dataflow.getDefinitions(read);
        const ReachingDefinitions::Chunk *chunk =
            findChunk(readDefinitions, unseenStack);
        check(readDefinitions.chunks().size() == 1 && chunk &&
                  chunk->hasUnknownDefinition() &&
                  chunk->hasIncomingDefinition() &&
                  chunk->definitions().empty(),
              "an exact stack-pointer may-write must preserve and contaminate a newly observed frame interval");
    }

    /* An incomplete call can modify any tracked non-register domain, even
     * when that domain had no represented intervals at invalidation time. */
    {
        const MemoryLocation unseenCustomMemory(
            MemoryDomain::USER + 7, 0x240, 64);
        ReachingDefinitions definitions;
        TrackedMemoryInvalidation invalidation(
            TrackedMemoryInvalidation::ALL_TRACKED_MEMORY);
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&invalidation, definitions);

        std::unique_ptr<Term> readStorage(
            new MemoryLocationAccess(unseenCustomMemory));
        Term *read = readStorage.get();
        Touch readStatement(std::move(readStorage), Term::READ);
        analyzer.execute(&readStatement, definitions);

        const ReachingDefinitions &readDefinitions =
            dataflow.getDefinitions(read);
        const ReachingDefinitions::Chunk *chunk =
            findChunk(readDefinitions, unseenCustomMemory);
        check(readDefinitions.chunks().size() == 1 && chunk &&
                  chunk->hasUnknownDefinition() &&
                  chunk->hasIncomingDefinition() &&
                  chunk->definitions().empty(),
              "all-tracked-memory invalidation must preserve and affect a newly observed non-stack interval");
    }

    /* A subsequent definite store establishes the current value for exactly
     * its written range.  It must shadow the older domain-wide may-write
     * there without making untouched ranges look definite. */
    {
        const MemoryLocation overwrittenStack(
            MemoryDomain::STACK, 64, 32);
        const MemoryLocation adjacentStack(
            MemoryDomain::STACK, 96, 32);
        ReachingDefinitions definitions;
        std::vector<std::unique_ptr<Term>> candidates;
        candidates.push_back(std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::ZERO_STACK_OFFSET, 64)));
        TrackedMemoryInvalidation invalidation(std::move(candidates));
        Dataflow dataflow;
        DataflowAnalyzer analyzer(
            dataflow, &architecture, canceled, log);
        analyzer.execute(&invalidation, definitions);

        Assignment definiteWrite(
            std::unique_ptr<Term>(new MemoryLocationAccess(
                overwrittenStack)),
            constant(32, 0x31415926));
        Term *write = definiteWrite.left();
        analyzer.execute(&definiteWrite, definitions);

        std::unique_ptr<Term> overwrittenReadStorage(
            new MemoryLocationAccess(overwrittenStack));
        Term *overwrittenRead = overwrittenReadStorage.get();
        Touch overwrittenReadStatement(
            std::move(overwrittenReadStorage), Term::READ);
        analyzer.execute(&overwrittenReadStatement, definitions);

        const ReachingDefinitions &overwrittenDefinitions =
            dataflow.getDefinitions(overwrittenRead);
        const ReachingDefinitions::Chunk *overwrittenChunk =
            findChunk(overwrittenDefinitions, overwrittenStack);
        check(overwrittenDefinitions.chunks().size() == 1 &&
                  overwrittenChunk &&
                  !overwrittenChunk->hasUnknownDefinition() &&
                  !overwrittenChunk->hasIncomingDefinition() &&
                  overwrittenChunk->definitions().size() == 1 &&
                  overwrittenChunk->definitions().front() == write,
              "a definite store must shadow an older domain-wide invalidation for its exact range");

        std::unique_ptr<Term> adjacentReadStorage(
            new MemoryLocationAccess(adjacentStack));
        Term *adjacentRead = adjacentReadStorage.get();
        Touch adjacentReadStatement(
            std::move(adjacentReadStorage), Term::READ);
        analyzer.execute(&adjacentReadStatement, definitions);

        const ReachingDefinitions &adjacentDefinitions =
            dataflow.getDefinitions(adjacentRead);
        const ReachingDefinitions::Chunk *adjacentChunk =
            findChunk(adjacentDefinitions, adjacentStack);
        check(adjacentDefinitions.chunks().size() == 1 && adjacentChunk &&
                  adjacentChunk->hasUnknownDefinition() &&
                  adjacentChunk->hasIncomingDefinition() &&
                  adjacentChunk->definitions().empty(),
              "a definite store must not shadow either alternative of a domain-wide invalidation outside its range");
    }
}

void testUnseenOpaqueWriteAcrossAlternatives() {
    const MemoryLocation unseenStack(
        MemoryDomain::STACK, 0x180, 32);

    for (int invalidatingPredecessorFirst = 0;
         invalidatingPredecessorFirst < 2;
         ++invalidatingPredecessorFirst)
    {
        Function function;
        BasicBlock *entry = addBlock(function);
        BasicBlock *firstPredecessor = addBlock(function);
        BasicBlock *secondPredecessor = addBlock(function);
        BasicBlock *join = addBlock(function);
        BasicBlock *invalidatingPredecessor =
            invalidatingPredecessorFirst ?
                firstPredecessor : secondPredecessor;
        BasicBlock *bypassPredecessor =
            invalidatingPredecessorFirst ?
                secondPredecessor : firstPredecessor;
        function.setEntry(entry);

        entry->pushBack(std::unique_ptr<Statement>(new Jump(
            std::unique_ptr<Term>(new Intrinsic(Intrinsic::UNKNOWN, 1)),
            JumpTarget(invalidatingPredecessor),
            JumpTarget(bypassPredecessor))));
        invalidatingPredecessor->pushBack(std::unique_ptr<Statement>(
            new TrackedMemoryInvalidation(
                TrackedMemoryInvalidation::ALL_TRACKED_MEMORY)));
        invalidatingPredecessor->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));
        bypassPredecessor->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(join))));

        std::unique_ptr<Term> readStorage(
            new MemoryLocationAccess(unseenStack));
        Term *read = readStorage.get();
        join->pushBack(std::unique_ptr<Statement>(
            new Touch(std::move(readStorage), Term::READ)));
        join->pushBack(std::unique_ptr<Statement>(new Halt()));

        TestArchitecture architecture;
        CancellationToken canceled;
        LogToken log;
        Dataflow dataflow;
        CFG cfg(function.basicBlocks());
        DataflowAnalyzer(
            dataflow, &architecture, canceled, log).analyze(cfg);

        const ReachingDefinitions &readDefinitions =
            dataflow.getDefinitions(read);
        const ReachingDefinitions::Chunk *chunk =
            findChunk(readDefinitions, unseenStack);
        check(dataflow.converged() &&
                  readDefinitions.chunks().size() == 1 && chunk &&
                  chunk->hasUnknownDefinition() &&
                  chunk->hasIncomingDefinition() &&
                  chunk->definitions().empty(),
              "an opaque write on one CFG alternative must join with a bypass as unknown plus incoming regardless of predecessor order");
    }
}

void testWildcardAlternativesSurviveDefinitionFiltering() {
    const MemoryLocation location(
        MemoryDomain::STACK, 0x200, 32);
    MemoryLocationAccess disappearingDefinition(location);
    MemoryLocationAccess survivingDefinition(location);

    for (int wildcardIsReceiver = 0;
         wildcardIsReceiver < 2;
         ++wildcardIsReceiver)
    {
        for (int accumulatedStateIsReceiver = 0;
             accumulatedStateIsReceiver < 2;
             ++accumulatedStateIsReceiver)
        {
            ReachingDefinitions wildcard;
            wildcard.addUnknownDomainDefinitions(false, true, false);
            ReachingDefinitions firstExact;
            firstExact.addDefinition(
                location, &disappearingDefinition);

            ReachingDefinitions accumulated;
            if (wildcardIsReceiver) {
                accumulated = wildcard;
                accumulated.joinAlternative(firstExact);
            } else {
                accumulated = firstExact;
                accumulated.joinAlternative(wildcard);
            }
            accumulated.filterOut(
                [&disappearingDefinition](
                    const MemoryLocation &, const Term *term) {
                    return term == &disappearingDefinition;
                });

            ReachingDefinitions secondExact;
            secondExact.addDefinition(
                location, &survivingDefinition);
            ReachingDefinitions joined;
            if (accumulatedStateIsReceiver) {
                joined = accumulated;
                joined.joinAlternative(secondExact);
            } else {
                joined = secondExact;
                joined.joinAlternative(accumulated);
            }

            const ReachingDefinitions projected =
                joined.projected(location);
            const ReachingDefinitions::Chunk *chunk =
                findChunk(projected, location);
            check(projected.chunks().size() == 1 && chunk &&
                      chunk->hasUnknownDefinition() &&
                      chunk->hasIncomingDefinition() &&
                      chunk->definitions().size() == 1 &&
                      chunk->definitions().front() ==
                          &survivingDefinition,
                  "filtered exact alternatives must retain wildcard and incoming domain defaults in either join order");
        }
    }
}

void testPathCompleteProvenance() {
    const MemoryLocation available(
        MemoryDomain::FIRST_REGISTER, 0, 32);
    const MemoryLocation branchLocal(
        MemoryDomain::FIRST_REGISTER + 1, 0, 32);
    const MemoryLocation clobbered(
        MemoryDomain::FIRST_REGISTER + 2, 0, 32);
    const MemoryLocation sink(
        MemoryDomain::FIRST_REGISTER + 3, 0, 32);
    const MemoryLocation branchSink(
        MemoryDomain::FIRST_REGISTER + 4, 0, 32);
    const MemoryLocation clobberSink(
        MemoryDomain::FIRST_REGISTER + 5, 0, 32);

    Function function;
    BasicBlock *entry = addBlock(function);
    BasicBlock *left = addBlock(function);
    BasicBlock *right = addBlock(function);
    BasicBlock *join = addBlock(function);
    function.setEntry(entry);

    Term *availableDefinition = addDefinition(
        entry, available, constant(32, 7));
    Term *clobberedDefinition = addDefinition(
        entry, clobbered, constant(32, 9));
    ReadDefinition validRead = addReadDefinition(entry, available, sink);
    entry->pushBack(std::unique_ptr<Statement>(
        new Call(constant(32, 0x1000))));
    entry->pushBack(std::unique_ptr<Statement>(new Jump(
        constant(1, 1), JumpTarget(left), JumpTarget(right))));

    Term *branchDefinition = addDefinition(
        left, branchLocal, constant(32, 11));
    left->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(join))));
    right->pushBack(std::unique_ptr<Statement>(new Jump(JumpTarget(join))));

    ReadDefinition missingPathRead = addReadDefinition(
        join, branchLocal, branchSink);
    ReadDefinition postCallRead = addReadDefinition(
        join, clobbered, clobberSink);
    join->pushBack(std::unique_ptr<Statement>(new Halt()));

    Dataflow dataflow;
    dataflow.setMemoryLocation(availableDefinition, available);
    dataflow.setMemoryLocation(clobberedDefinition, clobbered);
    dataflow.setMemoryLocation(branchDefinition, branchLocal);
    dataflow.setMemoryLocation(validRead.read, available);
    dataflow.setMemoryLocation(validRead.definition, sink);
    dataflow.setMemoryLocation(missingPathRead.read, branchLocal);
    dataflow.setMemoryLocation(missingPathRead.definition, branchSink);
    dataflow.setMemoryLocation(postCallRead.read, clobbered);
    dataflow.setMemoryLocation(postCallRead.definition, clobberSink);

    dataflow.getDefinitions(validRead.read).addDefinition(
        available, availableDefinition);
    /* Deliberately emulate the legacy RD merge: it can report a sole,
     * bit-complete definition even though the right predecessor has none. */
    dataflow.getDefinitions(missingPathRead.read).addDefinition(
        branchLocal, branchDefinition);
    dataflow.getDefinitions(postCallRead.read).addDefinition(
        clobbered, clobberedDefinition);

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    Dominators dominators(cfg, canceled, entry);
    DefUseGraph defUse(dataflow);
    ValueProvenance provenance(dataflow, defUse, dominators, cfg);

    check(provenance.isPathComplete(validRead.read),
          "a unique dominating definition before the use must be accepted");
    check(!provenance.isPathComplete(missingPathRead.read),
          "a branch-local definition must not cover the missing path");
    check(!provenance.isPathComplete(postCallRead.read),
          "a register value must not survive an opaque call without a clobber fact");
}

void testExpressionIdentityAndWidths() {
    const MemoryLocation source(
        MemoryDomain::FIRST_REGISTER + 10, 0, 32);
    const MemoryLocation firstSink(
        MemoryDomain::FIRST_REGISTER + 11, 0, 32);
    const MemoryLocation secondSink(
        MemoryDomain::FIRST_REGISTER + 12, 0, 32);
    const MemoryLocation narrowSink(
        MemoryDomain::FIRST_REGISTER + 13, 0, 32);
    const MemoryLocation wideSink(
        MemoryDomain::FIRST_REGISTER + 14, 0, 64);

    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);
    Term *sourceDefinition = addDefinition(
        block, source, constant(32, 3));

    std::unique_ptr<Term> firstReadStorage(
        new MemoryLocationAccess(source));
    Term *firstRead = firstReadStorage.get();
    std::unique_ptr<Term> firstExpressionStorage(new BinaryOperator(
        BinaryOperator::ADD, std::move(firstReadStorage), constant(32, 4), 32));
    Term *firstExpression = firstExpressionStorage.get();
    Term *firstDefinition = addDefinition(
        block, firstSink, std::move(firstExpressionStorage));

    std::unique_ptr<Term> secondReadStorage(
        new MemoryLocationAccess(source));
    Term *secondRead = secondReadStorage.get();
    std::unique_ptr<Term> secondExpressionStorage(new BinaryOperator(
        BinaryOperator::ADD, constant(32, 4),
        std::move(secondReadStorage), 32));
    Term *secondExpression = secondExpressionStorage.get();
    Term *secondDefinition = addDefinition(
        block, secondSink, std::move(secondExpressionStorage));

    Term *narrowConstant = nullptr;
    Term *narrowDefinition = addDefinition(
        block, narrowSink, constant(32, 0xffffffffU), &narrowConstant);
    Term *wideConstant = nullptr;
    Term *wideDefinition = addDefinition(
        block, wideSink, constant(64, 0xffffffffU), &wideConstant);
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    Dataflow dataflow;
    dataflow.setMemoryLocation(sourceDefinition, source);
    dataflow.setMemoryLocation(firstRead, source);
    dataflow.setMemoryLocation(firstDefinition, firstSink);
    dataflow.setMemoryLocation(secondRead, source);
    dataflow.setMemoryLocation(secondDefinition, secondSink);
    dataflow.setMemoryLocation(narrowDefinition, narrowSink);
    dataflow.setMemoryLocation(wideDefinition, wideSink);
    dataflow.getDefinitions(firstRead).addDefinition(
        source, sourceDefinition);
    dataflow.getDefinitions(secondRead).addDefinition(
        source, sourceDefinition);
    dataflow.setConverged(true);

    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    Dominators dominators(cfg, canceled, block);
    DefUseGraph defUse(dataflow);
    ValueProvenance provenance(dataflow, defUse, dominators, cfg);
    ExpressionIdentity identity(dataflow, defUse, provenance);

    check(identity.areIdentical(firstRead, secondRead),
          "reads with one exact complete definition must be identical");
    check(identity.areIdentical(firstExpression, secondExpression),
          "commutative operands may be reordered without changing identity");
    check(!identity.areIdentical(narrowConstant, wideConstant),
          "equal bit patterns of different widths must not be identical");

    dataflow.setConverged(false);
    check(!identity.areIdentical(firstExpression, secondExpression),
          "identity must not consume an unfinished dataflow iteration");
}

void testDataflowRevisionAndConvergence() {
    const MemoryLocation destination(
        MemoryDomain::FIRST_REGISTER + 20, 0, 32);
    std::unique_ptr<Term> sourceStorage = constant(32, 1);
    Term *source = sourceStorage.get();
    std::unique_ptr<Term> destinationStorage(
        new MemoryLocationAccess(destination));
    Term *write = destinationStorage.get();
    Assignment assignment(
        std::move(destinationStorage), std::move(sourceStorage));

    Dataflow dataflow;
    check(dataflow.incomplete(),
          "a fresh dataflow must not advertise an analysis fixpoint");
    Value *value = dataflow.getValue(source);
    const std::size_t creationRevision = dataflow.valueRevision();
    check(creationRevision > 0 && dataflow.incomplete(),
          "creating a tracked value must invalidate convergence");

    Dataflow runningDataflow;
    Value *runningValue = runningDataflow.getValue(source);
    runningDataflow.setAnalysisStatus(DataflowStatus::RUNNING);
    runningValue->setAbstractValue(SizedValue(32, 3));
    check(runningDataflow.running(),
          "lattice changes during analysis must preserve the RUNNING state");

    dataflow.setConverged(true);
    value->setAbstractValue(AbstractValue(32, -1, -1));
    check(dataflow.valueRevision() == creationRevision &&
              dataflow.converged(),
          "a no-op abstract-value update must not perturb the fixpoint");

    value->setAbstractValue(SizedValue(32, 7));
    check(dataflow.valueRevision() == creationRevision + 1 &&
              !dataflow.converged(),
          "a semantic abstract-value change must invalidate convergence");
    dataflow.setConverged(true);
    value->setAbstractValue(SizedValue(32, 7));
    check(dataflow.valueRevision() == creationRevision + 1 &&
              dataflow.converged(),
          "repeating an abstract value must keep the fixpoint stable");

    dataflow.setMemoryLocation(write, destination);
    dataflow.setConverged(true);
    const std::size_t locationRevision = dataflow.memoryLocationRevision();
    dataflow.setMemoryLocation(write, destination);
    check(dataflow.memoryLocationRevision() == locationRevision &&
              dataflow.converged(),
          "repeating an address fact must keep the fixpoint stable");
    dataflow.setMemoryLocation(
        write, MemoryLocation(destination.domain(), destination.addr(), 16));
    check(dataflow.hasAmbiguousMemoryLocation(write) &&
              dataflow.memoryLocationRevision() == locationRevision + 1 &&
              !dataflow.converged(),
          "conflicting address widths must become ambiguous");

    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);
    block->pushBack(std::unique_ptr<Statement>(new Assignment(
        std::unique_ptr<Term>(new MemoryLocationAccess(destination)),
        constant(32, 5))));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));
    CFG cfg(function.basicBlocks());
    TestArchitecture architecture;
    CancellationToken canceled;
    LogToken log;
    Dataflow analyzed;
    DataflowAnalyzer analyzer(analyzed, &architecture, canceled, log);
    analyzer.analyze(cfg);
    check(analyzed.converged(),
          "finite synthetic IR must reach a dataflow fixpoint");
    const std::size_t stableValueRevision = analyzed.valueRevision();
    const std::size_t stableLocationRevision =
        analyzed.memoryLocationRevision();
    analyzer.analyze(cfg);
    check(analyzed.converged() &&
              analyzed.valueRevision() == stableValueRevision &&
              analyzed.memoryLocationRevision() == stableLocationRevision,
          "reanalyzing unchanged IR must leave analysis revisions stable");

    Touch absentStatement(constant(32, 0x55), Term::READ);
    const Dataflow &constAnalyzed = analyzed;
    const std::size_t revisionBeforeConstLookup = analyzed.valueRevision();
    check(constAnalyzed.getValue(absentStatement.term()) == nullptr &&
              analyzed.valueRevision() == revisionBeforeConstLookup &&
              analyzed.converged(),
          "const dataflow lookup must not create facts or change lifecycle state");
}

void testIterationLimitScalesWithCfg() {
    const int blockCount = 40;
    Function function;
    std::vector<BasicBlock *> blocks;
    for (int index = 0; index < blockCount; ++index) {
        blocks.push_back(addBlock(function));
    }
    function.setEntry(blocks.back());
    blocks.front()->pushBack(std::unique_ptr<Statement>(new Halt()));
    for (int index = 1; index < blockCount; ++index) {
        blocks[index]->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(blocks[index - 1]))));
    }

    TestArchitecture architecture;
    CancellationToken canceled;
    LogToken log;
    Dataflow dataflow;
    DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(
        CFG(function.basicBlocks()));
    check(dataflow.converged(),
          "a reverse-ordered finite CFG must not hit a fixed 30-pass limit");
}

void testIncompleteAnalysisState() {
    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    std::unique_ptr<Term> oscillatingStorage = constant(32, 0);
    Term *oscillating = oscillatingStorage.get();
    block->pushBack(std::unique_ptr<Statement>(
        new Touch(std::move(oscillatingStorage), Term::READ)));

    Dataflow dataflow;
    bool alternate = false;
    block->pushBack(std::unique_ptr<Statement>(new Callback([&]() {
        alternate = !alternate;
        dataflow.getValue(oscillating)->setAbstractValue(
            SizedValue(32, alternate ? 1 : 2));
    })));
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    TestArchitecture architecture;
    CancellationToken canceled;
    LogToken log;
    DataflowAnalyzer(dataflow, &architecture, canceled, log).analyze(
        CFG(function.basicBlocks()));
    check(dataflow.incomplete() && !dataflow.running(),
          "hitting the bounded iteration limit must produce INCOMPLETE");
}

void testIncompleteInstrumentationFinalization() {
    const ConstantValue targetAddress = 0x7100;
    const ConstantValue stableTargetAddress = 0x7200;
    const ByteAddr callAddress = 0x100000;
    const ByteAddr stableCallAddress = 0x100010;

    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);

    std::unique_ptr<Term> callTargetStorage =
        constant(32, targetAddress);
    Term *callTarget = callTargetStorage.get();
    std::unique_ptr<Call> callStorage(new Call(
        std::move(callTargetStorage)));
    Call *call = callStorage.get();
    TestInstruction instruction(callAddress, 5);
    call->setInstruction(&instruction);
    block->pushBack(std::move(callStorage));

    std::unique_ptr<Term> stableCallTargetStorage =
        constant(32, stableTargetAddress);
    Term *stableCallTarget = stableCallTargetStorage.get();
    std::unique_ptr<Call> stableCallStorage(new Call(
        std::move(stableCallTargetStorage)));
    Call *stableCall = stableCallStorage.get();
    TestInstruction stableInstruction(stableCallAddress, 5);
    stableCall->setInstruction(&stableInstruction);
    block->pushBack(std::move(stableCallStorage));

    std::unique_ptr<Term> returnTargetStorage = constant(32, 0x1234);
    Term *returnTarget = returnTargetStorage.get();
    std::unique_ptr<Jump> jumpStorage(new Jump(
        JumpTarget(std::move(returnTargetStorage))));
    Jump *jump = jumpStorage.get();
    block->pushBack(std::move(jumpStorage));

    TestConvention provisionalConvention;
    TestConvention callSiteConvention;
    calling::Conventions conventions;
    conventions.setConvention(
        calling::CalleeId(&function), &provisionalConvention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(targetAddress)),
        &provisionalConvention);
    conventions.setConvention(
        calling::CalleeId(calling::EntryAddress(stableTargetAddress)),
        &provisionalConvention);
    conventions.setConvention(
        calling::CalleeId(calling::CallAddress(stableCallAddress)),
        &callSiteConvention);
    calling::Signatures signatures;
    Dataflow dataflow;
    dataflow.setAnalysisStatus(DataflowStatus::RUNNING);
    dataflow.getValue(callTarget)->setAbstractValue(
        SizedValue(32, targetAddress));
    dataflow.getValue(stableCallTarget)->setAbstractValue(
        SizedValue(32, stableTargetAddress));
    dataflow.getValue(returnTarget)->makeReturnAddress();

    calling::Hooks hooks(conventions, signatures);
    hooks.instrument(&function, &dataflow);

    std::vector<const Callback *> callbacks;
    foreach (const Statement *statement, block->statements()) {
        if (const Callback *callback = statement->as<Callback>()) {
            callbacks.push_back(callback);
        }
    }
    foreach (const Callback *callback, callbacks) {
        callback->function()();
    }

    const calling::CallHook *provisionalCallHook =
        hooks.getCallHook(call);
    const calling::CallHook *stableCallHook =
        hooks.getCallHook(stableCall);
    const calling::ReturnHook *provisionalReturnHook =
        hooks.getReturnHook(jump);
    check(provisionalCallHook != nullptr &&
              stableCallHook != nullptr &&
              provisionalReturnHook != nullptr,
          "RUNNING callbacks must be able to install provisional hooks");
    check(calling::getCalleeId(call, dataflow).kind() ==
              calling::CalleeId::CALL_ADDR &&
              !dflow::isReturn(jump, dataflow),
          "ordinary clients must not consume RUNNING callee/return facts");

    const Term *oldSyntheticTerm = nullptr;
    foreach (const Statement *statement,
             provisionalCallHook->patch().insertedStatements()) {
        if (const Assignment *assignment = statement->asAssignment()) {
            oldSyntheticTerm = assignment->right();
            break;
        }
        if (const Touch *touch = statement->asTouch()) {
            oldSyntheticTerm = touch->term();
            break;
        }
    }
    check(oldSyntheticTerm != nullptr,
          "the provisional call hook must contain a synthetic term");
    dataflow.getValue(oldSyntheticTerm)->setAbstractValue(
        SizedValue(oldSyntheticTerm->size(), 0));

    dataflow.setAnalysisStatus(DataflowStatus::INCOMPLETE);
    const auto provisionalHookStatements = cgen::getHookStatements(
        &function, dataflow, hooks);
    foreach (const Statement *statement,
             provisionalCallHook->patch().insertedStatements()) {
        check(provisionalHookStatements.find(statement) !=
                  provisionalHookStatements.end(),
              "all synthetic call-hook statements must be hidden from code generation");
    }
    foreach (const Statement *statement,
             stableCallHook->patch().insertedStatements()) {
        check(provisionalHookStatements.find(statement) !=
                  provisionalHookStatements.end(),
              "stable call-site hook statements must be hidden from code generation");
    }
    foreach (const Statement *statement,
             provisionalReturnHook->patch().insertedStatements()) {
        check(provisionalHookStatements.find(statement) !=
                  provisionalHookStatements.end(),
              "return-hook statements must stay hidden when dataflow is incomplete");
    }

    conventions.setConvention(
        calling::CalleeId(calling::CallAddress(callAddress)),
        &callSiteConvention);
    hooks.finalizeInstrumentation(&function, dataflow);

    check(hooks.getCallHook(call) == nullptr,
          "INCOMPLETE finalization must remove a resolved-target call hook instead of adding unanalyzed terms");
    check(hooks.getCallHook(stableCall) == stableCallHook,
          "INCOMPLETE finalization must retain an analyzed call-site hook");
    check(hooks.getReturnHook(jump) == nullptr,
          "INCOMPLETE finalization must remove a provisional return hook");
    check(provisionalCallHook->patch().insertedStatements().empty() &&
              provisionalReturnHook->patch().insertedStatements().empty(),
          "removed patches must not retain stale inserted-statement pointers");
    check(dataflow.findValue(oldSyntheticTerm) == nullptr,
          "facts for detached provisional hook terms must be discarded");

    const auto finalHookStatements = cgen::getHookStatements(
        &function, dataflow, hooks);
    foreach (const Statement *statement, finalHookStatements) {
        check(provisionalHookStatements.find(statement) !=
                  provisionalHookStatements.end(),
              "INCOMPLETE finalization must not introduce any unanalyzed hook statement");
    }
    foreach (const Statement *statement,
             stableCallHook->patch().insertedStatements()) {
        check(finalHookStatements.find(statement) !=
                  finalHookStatements.end(),
              "conservative call-hook statements must be hidden when dataflow is incomplete");
    }
}

void testPointerAndAddressWidthSafety() {
    TestArchitecture architecture;
    CancellationToken canceled;
    LogToken log;
    ReachingDefinitions definitions;

    {
        Dataflow dataflow;
        DataflowAnalyzer analyzer(dataflow, &architecture, canceled, log);
        Touch read(std::unique_ptr<Term>(new Dereference(
            constant(64, (std::numeric_limits<ConstantValue>::max)()),
            MemoryDomain::MEMORY, 8)), Term::READ);
        analyzer.execute(&read, definitions);
        check(!dataflow.getMemoryLocation(read.term()),
              "a byte address that overflows the bit-address domain must be rejected");
    }

    {
        Dataflow dataflow;
        DataflowAnalyzer analyzer(dataflow, &architecture, canceled, log);
        const MemoryLocation result(
            MemoryDomain::FIRST_REGISTER + 30, 0, 32);
        std::unique_ptr<Term> wrapped(new BinaryOperator(
            BinaryOperator::ADD,
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::ZERO_STACK_OFFSET, 32)),
            constant(32, 0xffffffffU), 32));
        Term *wrappedTerm = wrapped.get();
        Assignment assignment(
            std::unique_ptr<Term>(new MemoryLocationAccess(result)),
            std::move(wrapped));
        analyzer.execute(&assignment, definitions);
        const Value *value = dataflow.getValue(wrappedTerm);
        check(value->isStackOffset() && value->stackOffset() == -1,
              "symbolic pointer arithmetic must wrap at its machine width");
    }

    {
        Dataflow dataflow;
        DataflowAnalyzer analyzer(dataflow, &architecture, canceled, log);
        const MemoryLocation result(
            MemoryDomain::FIRST_REGISTER + 31, 0, 64);
        std::unique_ptr<Term> extended(new UnaryOperator(
            UnaryOperator::ZERO_EXTEND,
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::ZERO_STACK_OFFSET, 32)), 64));
        Term *extendedTerm = extended.get();
        Assignment assignment(
            std::unique_ptr<Term>(new MemoryLocationAccess(result)),
            std::move(extended));
        analyzer.execute(&assignment, definitions);
        const Value *value = dataflow.getValue(extendedTerm);
        check(value->mayBeStackOffset() && !value->isStackOffset(),
              "changing pointer width must discard an unprovable exact frame offset");
    }
}

void testCheckedByteAddressBoundaries() {
    const ConstantValue maximumAddress = static_cast<ConstantValue>(
        (std::numeric_limits<ByteAddr>::max)());
    const ConstantValue maximumUnsigned =
        (std::numeric_limits<ConstantValue>::max)();

    CheckedByteRange range = {-3, -2, 1};
    check(checkedByteRange(maximumAddress, 0, range) &&
              range.begin == (std::numeric_limits<ByteAddr>::max)() &&
              range.end == (std::numeric_limits<ByteAddr>::max)() &&
              range.size == 0,
          "an empty range at the maximum signed byte address must remain representable");

    check(checkedByteRange(maximumAddress - 1, 1, range) &&
              range.begin == (std::numeric_limits<ByteAddr>::max)() - 1 &&
              range.end == (std::numeric_limits<ByteAddr>::max)() &&
              range.size == 1,
          "a one-byte range ending at the maximum signed byte address must be accepted");

    const CheckedByteRange unchangedRange = {-7, -5, 2};
    range = unchangedRange;
    check(!checkedByteRange(maximumAddress - 1, 2, range) &&
              range.begin == unchangedRange.begin &&
              range.end == unchangedRange.end &&
              range.size == unchangedRange.size,
          "a range whose exclusive end exceeds ByteAddr must be rejected without changing the result");

    range = unchangedRange;
    check(!checkedByteRange(maximumUnsigned, 1, range) &&
              range.begin == unchangedRange.begin &&
              range.end == unchangedRange.end &&
              range.size == unchangedRange.size,
          "an unsigned range that would wrap and narrow to a signed address must be rejected");

    check(checkedInclusiveByteRange(
              maximumAddress - 1, maximumAddress - 1, range) &&
              range.begin == (std::numeric_limits<ByteAddr>::max)() - 1 &&
              range.end == (std::numeric_limits<ByteAddr>::max)() &&
              range.size == 1,
          "a one-byte inclusive range below the maximum signed address must be accepted");

    range = unchangedRange;
    check(!checkedInclusiveByteRange(
              maximumAddress, maximumAddress, range) &&
              range.begin == unchangedRange.begin &&
              range.end == unchangedRange.end &&
              range.size == unchangedRange.size,
          "an inclusive maximum address must be rejected when its exclusive end is unrepresentable");

    ByteAddr address = -7;
    check(checkedByteAddressAdd(maximumAddress - 1, 1, address) &&
              address == (std::numeric_limits<ByteAddr>::max)(),
          "checked byte-address addition must accept an exactly representable sum");

    address = -7;
    check(!checkedByteAddressAdd(maximumAddress, 1, address) &&
              address == -7,
          "checked byte-address addition must reject signed overflow without changing the result");

    address = -7;
    check(!checkedByteAddressAdd(maximumUnsigned, 1, address) &&
              address == -7,
          "checked byte-address addition must reject unsigned wrap without changing the result");

    const ByteAddr maximum = (std::numeric_limits<ByteAddr>::max)();
    const CheckedByteRange outer = {maximum - 3, maximum, 3};
    const CheckedByteRange lastByte = {maximum - 1, maximum, 1};
    const CheckedByteRange emptyAtEnd = {maximum, maximum, 0};
    check(containsByteRange(outer, lastByte) &&
              containsByteRange(outer, emptyAtEnd),
          "well-formed ranges at the maximum representable endpoint must be contained");

    const CheckedByteRange negative = {-1, 0, 1};
    const CheckedByteRange reversed = {maximum - 1, maximum - 2, -1};
    const CheckedByteRange mismatchedSize = {
        maximum - 1, maximum, 2};
    const CheckedByteRange escaping = {
        maximum - 4, maximum - 2, 2};
    check(!containsByteRange(outer, negative) &&
              !containsByteRange(outer, reversed) &&
              !containsByteRange(outer, mismatchedSize) &&
              !containsByteRange(outer, escaping),
          "negative, reversed, size-inconsistent, and escaping ranges must not be contained");
}

void testDisassemblerAtMaximumByteAddress() {
    const ByteAddr maximum = (std::numeric_limits<ByteAddr>::max)();
    const ByteAddr begin = maximum - 3;
    TestDisassemblyArchitecture architecture;
    TopAddressByteSource source(begin, maximum);
    image::Image image;
    CancellationToken canceled;

    TestDisassembler disassembler(&architecture, 1);
    std::vector<ByteAddr> decodedAddresses;
    disassembler.disassemble(
        &image, &source, begin, maximum,
        [&decodedAddresses](std::shared_ptr<arch::Instruction> instruction) {
            decodedAddresses.push_back(instruction->addr());
        }, canceled);
    check(decodedAddresses.size() == 3 &&
              decodedAddresses[0] == begin &&
              decodedAddresses[1] == begin + 1 &&
              decodedAddresses[2] == maximum - 1,
          "disassembly must reach the final byte below the maximum exclusive endpoint");

    TopAddressByteSource overreportingSource(begin, maximum, true);
    TestDisassembler overreported(&architecture, 1);
    decodedAddresses.clear();
    overreported.disassemble(
        &image, &overreportingSource, begin, maximum,
        [&decodedAddresses](std::shared_ptr<arch::Instruction> instruction) {
            decodedAddresses.push_back(instruction->addr());
        }, canceled);
    check(decodedAddresses.empty() &&
              overreported.attemptedAddresses().size() == 3,
          "an overreported ByteSource result must not expose invalid bytes or prevent progress");

    TestDisassembler oversizedInstruction(&architecture, 4);
    decodedAddresses.clear();
    oversizedInstruction.disassemble(
        &image, &source, maximum - 2, maximum,
        [&decodedAddresses](std::shared_ptr<arch::Instruction> instruction) {
            decodedAddresses.push_back(instruction->addr());
        }, canceled);
    check(decodedAddresses.empty() &&
              oversizedInstruction.attemptedAddresses().size() == 2,
          "a decoded instruction larger than the remaining range must be rejected while making progress");

    image::Image relocatedImage;
    const image::Symbol *symbol = relocatedImage.addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::OBJECT, QLatin1String("top-relocation"),
            boost::none)));
    relocatedImage.addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(maximum - 1, symbol, 4)));
    TestDisassembler relocated(&architecture, 1);
    decodedAddresses.clear();
    relocated.disassemble(
        &relocatedImage, &source, maximum - 2, maximum,
        [&decodedAddresses](std::shared_ptr<arch::Instruction> instruction) {
            decodedAddresses.push_back(instruction->addr());
        }, canceled);
    check(decodedAddresses.size() == 1 &&
              decodedAddresses[0] == maximum - 2 &&
              relocated.attemptedAddresses().size() == 1,
          "a relocation larger than the remaining top-address range must terminate at the checked endpoint");
}

void testSafeBitShifts() {
    const ConstantValue pattern = UINT64_C(0x0123456789abcdef);
    const int width = std::numeric_limits<ConstantValue>::digits;
    const ConstantValue allBits =
        (std::numeric_limits<ConstantValue>::max)();

    check(bitMask<ConstantValue>(0) == 0 &&
              bitMask<ConstantValue>(-1) == 0 &&
              bitMask<ConstantValue>(
                  (std::numeric_limits<int>::min)()) == 0 &&
              bitMask<ConstantValue>(1) == 1 &&
              bitMask<ConstantValue>(width) == allBits &&
              bitMask<ConstantValue>(width + 1) == allBits,
          "bit masks must handle nonpositive and over-width counts without undefined shifts");

    check(shiftLeft(pattern, 4) == (pattern << 4) &&
              shiftRight(pattern, 4) == (pattern >> 4),
          "in-range bit shifts must preserve their ordinary integer semantics");
    check(shiftLeft(pattern, width) == 0 &&
              shiftLeft(pattern, width + 1) == 0 &&
              shiftRight(pattern, width) == 0 &&
              shiftRight(pattern, width + 1) == 0,
          "left and right shifts at or beyond the storage width must produce zero");
    check(shiftLeft(pattern, -1) == 0 &&
              shiftRight(pattern, -1) == 0,
          "direction-specific shift helpers must reject negative counts without undefined behavior");

    check(bitShift(pattern, 4) == (pattern << 4) &&
              bitShift(pattern, -4) == (pattern >> 4) &&
              bitShift(pattern, width) == 0 &&
              bitShift(pattern, -width) == 0 &&
              bitShift(pattern, (std::numeric_limits<int>::min)()) == 0,
          "signed-direction shifting must use a safe magnitude for both over-width directions");

    AbstractValue upperHalf(SizedValue(64, pattern));
    upperHalf.shift(-32);
    check(upperHalf.size() == 32 && upperHalf.isConcrete() &&
              upperHalf.asConcrete().value() == UINT64_C(0x01234567),
          "aligning a wider definition to its upper subrange must shift right by the absolute offset");
}

} // anonymous namespace

int main() {
    try {
        testDataflowRevisionAndConvergence();
        testIterationLimitScalesWithCfg();
        testIncompleteAnalysisState();
        testIncompleteInstrumentationFinalization();
        testDominanceAndPostDominance();
        testAlternativeReachingDefinitions();
        testLateFunctionEntryPreservesFallthrough();
        testLateEntryInsideIrlessTailPreservesFallthrough();
        testKnownIrlessFunctionEntryIsPreserved();
        testDirectCallBoundaryPreventsFunctionMerging();
        testOpaqueMayWriteInvalidation();
        testUnseenOpaqueWriteAcrossAlternatives();
        testWildcardAlternativesSurviveDefinitionFiltering();
        testCallClobberContract();
        testCallStackCleanupSoundness();
        testResolvedTargetOverridesCallSiteFallback();
        testCallerCleanupCallFrameInference();
        testInferredFunctionSignatureIsRevalidatedAcrossPasses();
        testWideReturnDefinitionKeepsUnusedLowHalfAcrossPasses();
        testSharedReturnDefinitionAcrossTwoReturnsIsStable();
        testInferredCallReturnIsRevalidatedAcrossPasses();
        testVariadicStackTailWithoutExtentIsRevalidated();
        testWideFixedAndVariadicStoreIsRevalidatedAcrossPasses();
        testSharedVariadicDefinitionAcrossTwoCallsIsStable();
        testCallSpecificVariadicArguments();
        testCallPointeeReadLiveness();
        testCallPointeeWriteInvalidation();
        testCallSnapshotDoesNotMaterializeControlReturnAddress();
        testPathCompleteProvenance();
        testExpressionIdentityAndWidths();
        testPointerAndAddressWidthSafety();
        testCheckedByteAddressBoundaries();
        testDisassemblerAtMaximumByteAddress();
        testSafeBitShifts();
    } catch (const std::exception &exception) {
        std::cerr << "analysis regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
