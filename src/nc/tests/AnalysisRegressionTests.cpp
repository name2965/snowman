/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <climits>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include <nc/common/CancellationToken.h>
#include <nc/common/Foreach.h>
#include <nc/common/LogToken.h>
#include <nc/common/SizedValue.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/PostDominators.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallSignature.h>
#include <nc/core/ir/calling/CallHook.h>
#include <nc/core/ir/calling/CalleeId.h>
#include <nc/core/ir/calling/Convention.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/EntryHook.h>
#include <nc/core/ir/calling/ReturnHook.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cgen/Utils.h>
#include <nc/core/ir/dflow/AbstractValue.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DataflowAnalyzer.h>
#include <nc/core/ir/dflow/DefUseGraph.h>
#include <nc/core/ir/dflow/ExpressionIdentity.h>
#include <nc/core/ir/dflow/ReachingDefinitions.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/dflow/ValueProvenance.h>
#include <nc/core/ir/liveness/Liveness.h>
#include <nc/core/ir/liveness/LivenessAnalyzer.h>
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
        signatures.setSignature(call, signature);
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
              (contractKind == NO_CALL_SIGNATURE),
          "only a call without a signature must use the inference snapshot");
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
    const CallEffectResult otherMemoryRead =
        analyzeCallEffect(false, true, false);
    check(!otherMemoryRead.stackStoreLive &&
              otherMemoryRead.otherMemoryStoreLive,
          "a definite non-stack call argument must preserve only non-register memory it may read");
    check(!analyzeCallEffect(true, false, true).stackStoreLive,
          "a call's write-only effect alone must not keep its incoming value live");
    check(analyzeCallEffect(true, true, true).stackStoreLive,
          "a read-write stack pointee must preserve its incoming value");
    const CallEffectResult defaultIncomplete = analyzeCallEffect(
        false, false, false, DEFAULT_INCOMPLETE_PROTOTYPE);
    check(defaultIncomplete.stackStoreLive &&
              defaultIncomplete.otherMemoryStoreLive,
          "a prototype without complete effects must preserve every memory definition the callee may read");
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

        const ReachingDefinitions::Chunk *chunk =
            findChunk(definitions, lowStack);
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

} // anonymous namespace

int main() {
    try {
        testDataflowRevisionAndConvergence();
        testIterationLimitScalesWithCfg();
        testIncompleteAnalysisState();
        testIncompleteInstrumentationFinalization();
        testDominanceAndPostDominance();
        testAlternativeReachingDefinitions();
        testOpaqueMayWriteInvalidation();
        testCallClobberContract();
        testCallPointeeReadLiveness();
        testCallPointeeWriteInvalidation();
        testPathCompleteProvenance();
        testExpressionIdentityAndWidths();
        testPointerAndAddressWidthSafety();
    } catch (const std::exception &exception) {
        std::cerr << "analysis regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
