/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <memory>
#include <stdexcept>
#include <vector>

#include <nc/core/Context.h>
#include <nc/core/MasterAnalyzer.h>
#include <nc/arch/x86/X86Registers.h>
#include <nc/core/arch/Register.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/arch/Instructions.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Section.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallSignature.h>
#include <nc/core/ir/calling/Convention.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/SignatureAnalyzer.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cflow/Graphs.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DataflowAnalyzer.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/idiom/Idioms.h>
#include <nc/core/ir/liveness/Liveness.h>
#include <nc/core/ir/liveness/LivenessAnalyzer.h>
#include <nc/core/ir/liveness/Livenesses.h>
#include <nc/core/ir/types/Types.h>
#include <nc/core/ir/vars/Variables.h>
#include <nc/core/likec/Tree.h>
#include <nc/core/irgen/InstructionAnalyzer.h>

using namespace nc;
using namespace nc::core;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

class EmptyInstructionAnalyzer: public irgen::InstructionAnalyzer {
protected:
    void doCreateStatements(
        const nc::core::arch::Instruction *, ir::Program *) override {}
};

class TestArchitecture: public nc::core::arch::Architecture {
public:
    TestArchitecture() {
        setName(QString("test"));
        setBitness(32);
        setMaxInstructionSize(2);
    }

    std::unique_ptr<nc::core::arch::Disassembler> createDisassembler()
            const override {
        return std::unique_ptr<nc::core::arch::Disassembler>();
    }

    std::unique_ptr<irgen::InstructionAnalyzer>
            createInstructionAnalyzer() const override {
        return std::unique_ptr<irgen::InstructionAnalyzer>(
            new EmptyInstructionAnalyzer());
    }

    ByteOrder getByteOrder(ir::Domain) const override {
        return ByteOrder::LittleEndian;
    }
};

class TestInstruction: public nc::core::arch::Instruction {
public:
    explicit TestInstruction(ByteAddr address):
        nc::core::arch::Instruction(address, 2)
    {}

    void print(QTextStream &) const override {}
};

class RegisterAbiConvention: public ir::calling::Convention {
public:
    RegisterAbiConvention(
            const char *name,
            const std::vector<std::vector<ir::MemoryLocation>> &groups):
        ir::calling::Convention(QString(name))
    {
        for (const auto &group : groups) {
            addArgumentGroup(group);
        }
    }
};

std::unique_ptr<ir::Term> semanticConstant(
        SmallBitSize size, ConstantValue value) {
    return std::unique_ptr<ir::Term>(
        new ir::Constant(SizedValue(size, value)));
}

ir::BasicBlock *addSemanticBlock(ir::Function &function) {
    std::unique_ptr<ir::BasicBlock> block(new ir::BasicBlock());
    ir::BasicBlock *result = block.get();
    function.addBasicBlock(std::move(block));
    return result;
}

ir::Statement *addRegisterDefinition(
        ir::BasicBlock *block, const ir::MemoryLocation &location,
        ConstantValue value) {
    std::unique_ptr<ir::Statement> statement(new ir::Assignment(
        std::unique_ptr<ir::Term>(new ir::MemoryLocationAccess(location)),
        semanticConstant(location.size<SmallBitSize>(), value)));
    ir::Statement *result = statement.get();
    block->pushBack(std::move(statement));
    return result;
}

ir::Call *addResolvedCall(
        ir::BasicBlock *block,
        const nc::core::arch::Instruction *instruction,
        ConstantValue target) {
    std::unique_ptr<ir::Call> call(new ir::Call(
        semanticConstant(32, target)));
    ir::Call *result = call.get();
    call->setInstruction(instruction);
    block->pushBack(std::move(call));
    return result;
}

void runSignatureSemanticPass(
        ir::Function &function, const TestArchitecture &architecture,
        ir::calling::Hooks &hooks, ir::calling::Signatures &signatures) {
    std::unique_ptr<ir::dflow::Dataflow> dataflow(
        new ir::dflow::Dataflow());
    hooks.instrument(&function, dataflow.get());

    CancellationToken canceled;
    LogToken log;
    ir::CFG cfg(function.basicBlocks());
    ir::dflow::DataflowAnalyzer(
        *dataflow, &architecture, canceled, log).analyze(cfg);
    hooks.finalizeInstrumentation(&function, *dataflow);
    check(dataflow->converged(),
          "the signature refinement fixture must reach a dataflow fixpoint");

    std::unique_ptr<ir::liveness::Liveness> liveness(
        new ir::liveness::Liveness());
    ir::liveness::LivenessAnalyzer(
        *liveness, &function, *dataflow, &architecture, nullptr,
        hooks, &signatures, log).analyze();

    ir::dflow::Dataflows dataflows;
    dataflows.emplace(
        &function,
        std::unique_ptr<const ir::dflow::Dataflow>(
            std::move(dataflow)));
    ir::liveness::Livenesses livenesses;
    livenesses.emplace(
        &function,
        std::unique_ptr<const ir::liveness::Liveness>(
            std::move(liveness)));

    signatures.beginInferenceUpdate();
    try {
        ir::calling::SignatureAnalyzer(
            signatures, dataflows, hooks, livenesses,
            canceled, log).analyze();
        signatures.finishInferenceUpdate();
    } catch (...) {
        signatures.cancelInferenceUpdate();
        throw;
    }
}

bool hasRegisterArguments(
        const std::shared_ptr<ir::calling::CallSignature> &signature,
        const std::vector<ir::MemoryLocation> &locations) {
    if (!signature || signature->arguments().size() != locations.size()) {
        return false;
    }
    for (std::size_t index = 0; index < locations.size(); ++index) {
        const ir::MemoryLocationAccess *access =
            signature->arguments()[index]->asMemoryLocationAccess();
        if (!access || access->memoryLocation() != locations[index]) {
            return false;
        }
    }
    return true;
}

void testFunctionSymbolsSeedProgramBoundaries() {
    TestArchitecture architecture;
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);

    std::unique_ptr<image::Section> executableSection(
        new image::Section(QString("code"), 0x1000, 0x100));
    executableSection->setAllocated();
    executableSection->setExecutable();
    image->addSection(std::move(executableSection));

    std::unique_ptr<image::Section> dataSection(
        new image::Section(QString("data"), 0x2000, 0x100));
    dataSection->setAllocated();
    image->addSection(std::move(dataSection));

    image->addSymbol(std::unique_ptr<image::Symbol>(new image::Symbol(
        image::SymbolType::FUNCTION, QString("exported"),
        boost::optional<ConstantValue>(0x1010))));
    image->addSymbol(std::unique_ptr<image::Symbol>(new image::Symbol(
        image::SymbolType::FUNCTION, QString("interior"),
        boost::optional<ConstantValue>(0x1011))));
    image->addSymbol(std::unique_ptr<image::Symbol>(new image::Symbol(
        image::SymbolType::FUNCTION, QString("data_function"),
        boost::optional<ConstantValue>(0x2010))));

    auto instructions =
        std::make_shared<nc::core::arch::Instructions>();
    instructions->add(std::make_shared<TestInstruction>(0x1010));
    instructions->add(std::make_shared<TestInstruction>(0x2010));

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    MasterAnalyzer().createProgram(context);

    check(context.program()->isFunctionEntry(0x1010),
          "executable FUNCTION symbol did not seed a program boundary");
    check(!context.program()->isFunctionEntry(0x1011),
          "interior-byte FUNCTION symbol manufactured an entry");
    check(!context.program()->isFunctionEntry(0x2010),
          "non-executable FUNCTION symbol manufactured an entry");
}

/*
 * Exercises MasterAnalyzer's orchestration without depending on an
 * architecture or a particular instruction sequence.  An external metadata
 * implementation reports newly proved entries for a configurable number of
 * rounds, while the remaining phases install sentinel analysis products.
 */
class RefinementAnalyzer: public MasterAnalyzer {
    const unsigned int refinementsBeforeStable_;
    const bool neverStabilizes_;

    mutable unsigned int functionBuilds_ = 0;
    mutable unsigned int dataflowPasses_ = 0;
    mutable unsigned int livenessPasses_ = 0;
    mutable unsigned int signaturePasses_ = 0;
    mutable unsigned int acceptedRefinements_ = 0;
    mutable std::vector<bool> refinementPermissions_;

    static void checkRestartState(const Context &context) {
        check(context.program() != nullptr,
              "boundary refinement must preserve the Program");
        check(context.functions() == nullptr,
              "restart retained Function pointers");
        check(context.conventions() == nullptr,
              "restart retained calling conventions");
        check(context.hooks() == nullptr,
              "restart retained statement hooks");
        check(context.signatures() == nullptr,
              "restart retained pointer-keyed signatures");
        check(context.dataflows() == nullptr,
              "restart retained pointer-keyed dataflows");
        check(context.variables() == nullptr,
              "restart retained pointer-keyed variables");
        check(context.graphs() == nullptr,
              "restart retained pointer-keyed structural graphs");
        check(context.livenesses() == nullptr,
              "restart retained pointer-keyed liveness");
        check(context.idioms() == nullptr,
              "restart retained pointer-keyed idioms");
        check(context.types() == nullptr,
              "restart retained pointer-keyed types");
        check(context.tree() == nullptr,
              "restart retained the generated syntax tree");
    }

    static void installLateAnalysisSentinels(Context &context) {
        context.setVariables(std::unique_ptr<ir::vars::Variables>(
            new ir::vars::Variables()));
        context.setGraphs(std::unique_ptr<ir::cflow::Graphs>(
            new ir::cflow::Graphs()));
        context.setIdioms(std::unique_ptr<ir::idiom::Idioms>(
            new ir::idiom::Idioms()));
        context.setTypes(std::unique_ptr<ir::types::Types>(
            new ir::types::Types()));
        context.setTree(std::unique_ptr<likec::Tree>(new likec::Tree()));
    }

public:
    RefinementAnalyzer(unsigned int refinementsBeforeStable,
                       bool neverStabilizes):
        refinementsBeforeStable_(refinementsBeforeStable),
        neverStabilizes_(neverStabilizes)
    {}

    unsigned int functionBuilds() const { return functionBuilds_; }
    unsigned int dataflowPasses() const { return dataflowPasses_; }
    unsigned int livenessPasses() const { return livenessPasses_; }
    unsigned int signaturePasses() const { return signaturePasses_; }
    unsigned int acceptedRefinements() const {
        return acceptedRefinements_;
    }
    const std::vector<bool> &refinementPermissions() const {
        return refinementPermissions_;
    }

    void createProgram(Context &context) const override {
        context.setProgram(
            std::unique_ptr<ir::Program>(new ir::Program()));
    }

    void createFunctions(Context &context) const override {
        if (functionBuilds_ != 0) {
            checkRestartState(context);
        }
        ++functionBuilds_;
        context.setFunctions(
            std::unique_ptr<ir::Functions>(new ir::Functions()));
    }

    void createHooks(Context &context) const override {
        context.setSignatures(
            std::unique_ptr<ir::calling::Signatures>(
                new ir::calling::Signatures()));
        context.setConventions(
            std::unique_ptr<ir::calling::Conventions>(
                new ir::calling::Conventions()));
        context.setHooks(std::unique_ptr<ir::calling::Hooks>(
            new ir::calling::Hooks(
                *context.conventions(), *context.signatures())));
    }

    void detectCallingConventions(Context &) const override {}

    void dataflowAnalysis(Context &context) const override {
        ++dataflowPasses_;
        context.setDataflows(
            std::unique_ptr<ir::dflow::Dataflows>(
                new ir::dflow::Dataflows()));
    }

    void livenessAnalysis(Context &context) const override {
        ++livenessPasses_;
        context.setLivenesses(
            std::unique_ptr<ir::liveness::Livenesses>(
                new ir::liveness::Livenesses()));
    }

    void reconstructSignatures(Context &) const override {
        ++signaturePasses_;
    }

    bool applyExternalSignatures(
            Context &context,
            bool allowProgramRefinement) const override {
        refinementPermissions_.push_back(
            allowProgramRefinement);

        const bool requiresRefinement = neverStabilizes_ ||
            acceptedRefinements_ < refinementsBeforeStable_;
        if (requiresRefinement && allowProgramRefinement) {
            ++acceptedRefinements_;
            installLateAnalysisSentinels(context);
        }
        return requiresRefinement;
    }

    void reconstructVariables(Context &) const override {}
    void structuralAnalysis(Context &) const override {}
    void analyzeIdioms(Context &) const override {}
    void reconstructTypes(Context &) const override {}
    void generateTree(Context &) const override {}
};

/* External contracts participate in the semantic fixed point independently
 * of function-boundary discovery. */
class SemanticRefinementAnalyzer: public RefinementAnalyzer {
    const bool oscillates_;
    const bool dropsAfterFirstApplication_;
    mutable unsigned int applications_ = 0;

public:
    explicit SemanticRefinementAnalyzer(
            bool oscillates, bool dropsAfterFirstApplication = false):
        RefinementAnalyzer(0, false), oscillates_(oscillates),
        dropsAfterFirstApplication_(dropsAfterFirstApplication)
    {}

    unsigned int applications() const { return applications_; }

    bool applyExternalSignatures(Context &context, bool) const override {
        auto signature =
            std::make_shared<ir::calling::FunctionSignature>();
        if (oscillates_ && applications_ % 2 != 0) {
            signature->setVariadic();
        }
        ++applications_;
        if (!dropsAfterFirstApplication_ || applications_ == 1) {
            context.signatures()->setSignature(
                static_cast<ByteAddr>(0x1000), signature,
                ir::calling::SignatureSource::EXTERNAL);
        }
        return false;
    }
};

class CancelingSemanticLimitAnalyzer: public SemanticRefinementAnalyzer {
    mutable unsigned int programBuilds_ = 0;

public:
    CancelingSemanticLimitAnalyzer(): SemanticRefinementAnalyzer(true) {}

    void createProgram(Context &context) const override {
        SemanticRefinementAnalyzer::createProgram(context);
        if (++programBuilds_ == 2) {
            CancellationToken token = context.cancellationToken();
            token.cancel();
        }
    }
};

/* Cancels at the boundary between a refreshed dataflow and the liveness pass
 * which would normally consume it.  Products from the preceding semantic
 * iteration must already have been invalidated at that boundary. */
class CancelingAfterDataflowRefreshAnalyzer:
    public SemanticRefinementAnalyzer {
    mutable unsigned int dataflowRefreshes_ = 0;
    mutable unsigned int livenessRefreshes_ = 0;

public:
    CancelingAfterDataflowRefreshAnalyzer():
        SemanticRefinementAnalyzer(false)
    {}

    void dataflowAnalysis(Context &context) const override {
        SemanticRefinementAnalyzer::dataflowAnalysis(context);
        if (++dataflowRefreshes_ == 2) {
            CancellationToken token = context.cancellationToken();
            token.cancel();
        }
    }

    void livenessAnalysis(Context &context) const override {
        SemanticRefinementAnalyzer::livenessAnalysis(context);
        if (++livenessRefreshes_ == 1) {
            /* These phases ordinarily run later, but installing sentinels
             * proves the invalidation rule covers every Dataflow consumer,
             * not only Livenesses. */
            context.setVariables(std::unique_ptr<ir::vars::Variables>(
                new ir::vars::Variables()));
            context.setGraphs(std::unique_ptr<ir::cflow::Graphs>(
                new ir::cflow::Graphs()));
            context.setIdioms(std::unique_ptr<ir::idiom::Idioms>(
                new ir::idiom::Idioms()));
            context.setTypes(std::unique_ptr<ir::types::Types>(
                new ir::types::Types()));
            context.setTree(std::unique_ptr<likec::Tree>(
                new likec::Tree()));
        }
    }
};

/* Convention-only metadata must drive the same semantic fixed point even
 * when no FunctionSignature object changes. */
class ConventionRefinementAnalyzer: public RefinementAnalyzer {
    const bool dropsAfterFirstApplication_;
    ir::calling::Convention convention_;
    mutable unsigned int applications_ = 0;

public:
    explicit ConventionRefinementAnalyzer(bool dropsAfterFirstApplication):
        RefinementAnalyzer(0, false),
        dropsAfterFirstApplication_(dropsAfterFirstApplication),
        convention_(QString("external-test"))
    {}

    unsigned int applications() const { return applications_; }

    bool applyExternalSignatures(Context &context, bool) const override {
        ++applications_;
        if (!dropsAfterFirstApplication_ || applications_ == 1) {
            const ir::calling::CalleeId calleeId(
                ir::calling::CallAddress(0x1234));
            context.conventions()->setExternalConvention(
                calleeId, &convention_);
            context.conventions()->setExternalStackArgumentsSize(
                calleeId, boost::optional<ByteSize>(12));
        }
        return false;
    }
};

/* Verifies that MasterAnalyzer treats the two external registries as one
 * transaction when a metadata provider fails partway through a pass. */
class ThrowingExternalAnalyzer: public RefinementAnalyzer {
    ir::calling::Convention convention_;

public:
    ThrowingExternalAnalyzer():
        RefinementAnalyzer(0, false),
        convention_(QString("throwing-test"))
    {}

    bool applyExternalSignatures(Context &context, bool) const override {
        const ir::calling::CalleeId calleeId(
            ir::calling::CallAddress(0x4321));
        context.signatures()->setSignature(
            static_cast<ByteAddr>(0x4321),
            std::make_shared<ir::calling::FunctionSignature>(),
            ir::calling::SignatureSource::EXTERNAL);
        context.conventions()->setExternalConvention(
            calleeId, &convention_);
        context.conventions()->setExternalStackArgumentsSize(
            calleeId, boost::optional<ByteSize>(8));
        throw std::runtime_error("external provider failure");
    }
};

/* Simulates an authoritative refinement which mutates Program and then
 * fails before its armed transaction can complete. */
class ThrowingArmedRefinementAnalyzer: public RefinementAnalyzer {
public:
    ThrowingArmedRefinementAnalyzer(): RefinementAnalyzer(0, false) {}

    bool applyExternalSignatures(
            Context &context, bool allowProgramRefinement) const override {
        if (!allowProgramRefinement) {
            return true;
        }
        context.program()->addFunctionEntry(0x5151);
        throw std::runtime_error("armed Program refinement failure");
    }
};

std::shared_ptr<ir::calling::FunctionSignature> makeSignature(
        int intrinsicKind) {
    auto signature = std::make_shared<ir::calling::FunctionSignature>();
    signature->arguments().push_back(
        std::make_shared<ir::Intrinsic>(intrinsicKind, 32));
    return signature;
}

std::shared_ptr<ir::calling::CallSignature> makeCallSignature(
        int intrinsicKind) {
    auto signature = std::make_shared<ir::calling::CallSignature>();
    signature->arguments().push_back(
        std::make_shared<ir::Intrinsic>(intrinsicKind, 32));
    return signature;
}

void testExternalTransactionsUseCommittedReadSnapshot() {
    ir::calling::Signatures signatures;
    const ByteAddr address = 0x8000;
    const ByteAddr newAddress = 0x8004;
    ir::Function function;
    ir::Call call(std::unique_ptr<ir::Term>(
        new ir::Constant(SizedValue(32, 0x9000))));

    const auto inferredAddress = makeSignature(ir::Intrinsic::UNKNOWN);
    const auto inferredFunction = makeSignature(ir::Intrinsic::UNKNOWN);
    const auto inferredCall = makeCallSignature(ir::Intrinsic::UNKNOWN);
    signatures.setSignature(
        address, inferredAddress,
        ir::calling::SignatureSource::INFERRED);
    signatures.setSignature(
        &function, inferredFunction,
        ir::calling::SignatureSource::INFERRED);
    signatures.setSignature(
        &call, inferredCall,
        ir::calling::SignatureSource::INFERRED);

    const auto oldAddress = makeSignature(ir::Intrinsic::UNDEFINED);
    const auto oldFunction = makeSignature(ir::Intrinsic::UNDEFINED);
    const auto oldCall = makeCallSignature(ir::Intrinsic::UNDEFINED);
    signatures.setSignature(
        address, oldAddress, ir::calling::SignatureSource::EXTERNAL);
    signatures.setSignature(
        &function, oldFunction,
        ir::calling::SignatureSource::EXTERNAL);
    signatures.setSignature(
        &call, oldCall, ir::calling::SignatureSource::EXTERNAL);

    const auto newAddressSignature =
        makeSignature(ir::Intrinsic::ZERO_STACK_OFFSET);
    const auto newFunctionSignature =
        makeSignature(ir::Intrinsic::ZERO_STACK_OFFSET);
    const auto newCallSignature =
        makeCallSignature(ir::Intrinsic::ZERO_STACK_OFFSET);
    const auto stagedOnly = makeSignature(ir::Intrinsic::UNDEFINED);

    signatures.beginExternalUpdate();
    signatures.setSignature(
        address, newAddressSignature,
        ir::calling::SignatureSource::EXTERNAL);
    signatures.setSignature(
        &function, newFunctionSignature,
        ir::calling::SignatureSource::EXTERNAL);
    signatures.setSignature(
        &call, newCallSignature,
        ir::calling::SignatureSource::EXTERNAL);
    signatures.setSignature(
        newAddress, stagedOnly,
        ir::calling::SignatureSource::EXTERNAL);

    check(signatures.getSignature(address).get() == oldAddress.get() &&
              signatures.getSignature(
                  address,
                  ir::calling::SignatureSource::EXTERNAL).get() ==
                  oldAddress.get(),
          "address signature getter exposed an uncommitted snapshot");
    check(signatures.getSignature(&function).get() == oldFunction.get() &&
              signatures.getSignature(
                  &function,
                  ir::calling::SignatureSource::EXTERNAL).get() ==
                  oldFunction.get(),
          "function signature getter exposed an uncommitted snapshot");
    check(signatures.getSignature(&call).get() == oldCall.get() &&
              signatures.getSignature(
                  &call,
                  ir::calling::SignatureSource::EXTERNAL).get() ==
                  oldCall.get(),
          "call signature getter exposed an uncommitted snapshot");
    check(!signatures.getSignature(
              newAddress,
              ir::calling::SignatureSource::EXTERNAL),
          "new staged signature became readable before commit");

    signatures.finishExternalUpdate();
    check(signatures.getSignature(address).get() ==
              newAddressSignature.get() &&
              signatures.getSignature(&function).get() ==
                  newFunctionSignature.get() &&
              signatures.getSignature(&call).get() ==
                  newCallSignature.get() &&
              signatures.getSignature(newAddress).get() == stagedOnly.get(),
          "committed signature snapshot did not become visible atomically");

    ir::calling::Conventions conventions;
    ir::calling::Convention fallback(QString("fallback"));
    ir::calling::Convention oldConvention(QString("old-external"));
    ir::calling::Convention newConvention(QString("new-external"));
    const ir::calling::CalleeId existingId(
        ir::calling::CallAddress(0x8100));
    const ir::calling::CalleeId stagedOnlyId(
        ir::calling::CallAddress(0x8104));

    conventions.setFallbackConvention(existingId, &fallback);
    conventions.setFallbackConvention(stagedOnlyId, &fallback);
    conventions.setStackArgumentsSize(
        existingId, boost::optional<ByteSize>(4));
    conventions.setStackArgumentsSize(
        stagedOnlyId, boost::optional<ByteSize>(4));
    conventions.setExternalConvention(existingId, &oldConvention);
    conventions.setExternalStackArgumentsSize(
        existingId, boost::optional<ByteSize>(8));

    conventions.beginExternalUpdate();
    conventions.setExternalConvention(existingId, &newConvention);
    conventions.setExternalStackArgumentsSize(
        existingId, boost::optional<ByteSize>(16));
    conventions.setExternalConvention(stagedOnlyId, &newConvention);
    conventions.setExternalStackArgumentsSize(stagedOnlyId, boost::none);

    check(conventions.getConvention(existingId) == &oldConvention &&
              conventions.getExternalConvention(existingId) ==
                  &oldConvention &&
              conventions.getStackArgumentsSize(existingId) &&
              *conventions.getStackArgumentsSize(existingId) == 8 &&
              conventions.getExternalStackArgumentsSize(existingId) &&
              *conventions.getExternalStackArgumentsSize(existingId) == 8 &&
              conventions.hasExternalStackArgumentsSizeBinding(existingId) &&
              !conventions.isFallbackConvention(existingId),
          "convention getter exposed an uncommitted replacement");
    check(conventions.getConvention(stagedOnlyId) == &fallback &&
              !conventions.getExternalConvention(stagedOnlyId) &&
              conventions.getStackArgumentsSize(stagedOnlyId) &&
              *conventions.getStackArgumentsSize(stagedOnlyId) == 4 &&
              !conventions.getExternalStackArgumentsSize(stagedOnlyId) &&
              !conventions.hasExternalStackArgumentsSizeBinding(
                  stagedOnlyId) &&
              conventions.isFallbackConvention(stagedOnlyId),
          "new staged convention became readable before commit");

    conventions.finishExternalUpdate();
    check(conventions.getConvention(existingId) == &newConvention &&
              conventions.getExternalConvention(existingId) ==
                  &newConvention &&
              conventions.getStackArgumentsSize(existingId) &&
              *conventions.getStackArgumentsSize(existingId) == 16,
          "committed convention replacement did not become visible");
    check(conventions.getConvention(stagedOnlyId) == &newConvention &&
              conventions.getExternalConvention(stagedOnlyId) ==
                  &newConvention &&
              conventions.hasExternalStackArgumentsSizeBinding(
                  stagedOnlyId) &&
              !conventions.getExternalStackArgumentsSize(stagedOnlyId) &&
              !conventions.getStackArgumentsSize(stagedOnlyId) &&
              !conventions.isFallbackConvention(stagedOnlyId),
          "committed unknown-size convention did not mask fallback facts");
}

void testSignatureProvenancePreservesBothLayers() {
    ir::calling::Signatures signatures;
    const ByteAddr address = 0x1000;

    const auto inferred = makeSignature(ir::Intrinsic::UNKNOWN);
    check(signatures.setSignature(
              address, inferred, ir::calling::SignatureSource::INFERRED),
          "initial inferred signature did not change the registry");
    const std::uint64_t inferredRevision = signatures.revision();

    const auto equivalent = makeSignature(ir::Intrinsic::UNKNOWN);
    check(!signatures.setSignature(
              address, equivalent, ir::calling::SignatureSource::INFERRED),
          "structurally equal inference advanced the semantic state");
    check(signatures.revision() == inferredRevision,
          "equal inferred replacement advanced the revision");
    check(signatures.getSignature(address).get() == inferred.get(),
          "equal inferred replacement discarded the stable identity");

    const auto external = makeSignature(ir::Intrinsic::UNDEFINED);
    check(signatures.setSignature(
              address, external, ir::calling::SignatureSource::EXTERNAL),
          "external signature did not create a provenance layer");
    check(signatures.getSignature(address).get() == external.get(),
          "external signature did not override effective inference");

    const auto latestInference =
        makeSignature(ir::Intrinsic::ZERO_STACK_OFFSET);
    check(signatures.setSignature(
              address, latestInference,
              ir::calling::SignatureSource::INFERRED),
          "inference hidden by metadata was not tracked");
    check(signatures.getSignature(address).get() == external.get(),
          "new inference replaced an authoritative contract");
    check(signatures.getSignature(
              address, ir::calling::SignatureSource::INFERRED).get() ==
              latestInference.get(),
          "latest inferred layer was not retained under metadata");

    const std::uint64_t beforeEquivalentSnapshot = signatures.revision();
    signatures.beginInferenceUpdate();
    signatures.setSignature(
        address, makeSignature(ir::Intrinsic::ZERO_STACK_OFFSET),
        ir::calling::SignatureSource::INFERRED);
    signatures.finishInferenceUpdate();
    check(signatures.revision() == beforeEquivalentSnapshot,
          "equivalent inference snapshot did not reach a fixed point");
    check(signatures.getSignature(
              address, ir::calling::SignatureSource::INFERRED).get() ==
              latestInference.get(),
          "equivalent snapshot changed a stable signature identity");

    const std::uint64_t beforeExternalRemoval = signatures.revision();
    signatures.beginExternalUpdate();
    signatures.finishExternalUpdate();
    check(signatures.revision() == beforeExternalRemoval + 1,
          "omitted external metadata did not change the snapshot");
    check(!signatures.getSignature(
              address, ir::calling::SignatureSource::EXTERNAL),
          "stale external contract survived a complete snapshot");
    check(signatures.getSignature(address).get() == latestInference.get(),
          "removing metadata did not reveal current inference");

    signatures.setSignature(
        address, external, ir::calling::SignatureSource::EXTERNAL);

    signatures.beginInferenceUpdate();
    signatures.finishInferenceUpdate();
    check(!signatures.getSignature(
              address, ir::calling::SignatureSource::INFERRED),
          "stale inferred signature survived a complete snapshot");
    check(signatures.getSignature(address).get() == external.get(),
          "removing inference also removed the external contract");
}

void testConventionProvenanceUsesReplacementSnapshots() {
    ir::calling::Conventions conventions;
    ir::calling::Convention fallback(QString("fallback"));
    ir::calling::Convention external(QString("external"));
    ir::calling::Convention discarded(QString("discarded"));
    const ir::calling::CalleeId calleeId(
        ir::calling::CallAddress(0x2000));

    conventions.setFallbackConvention(calleeId, &fallback);
    conventions.setStackArgumentsSize(
        calleeId, boost::optional<ByteSize>(4));
    const std::uint64_t persistentRevision = conventions.revision();

    conventions.beginExternalUpdate();
    conventions.setExternalConvention(calleeId, &external);
    conventions.setExternalStackArgumentsSize(
        calleeId, boost::optional<ByteSize>(8));
    conventions.finishExternalUpdate();
    check(conventions.revision() == persistentRevision + 1,
          "external convention snapshot did not advance the revision once");
    check(conventions.getConvention(calleeId) == &external,
          "external convention did not override persistent fallback");
    check(!conventions.isFallbackConvention(calleeId),
          "external convention was reported as a fallback");
    check(conventions.getStackArgumentsSize(calleeId) &&
              *conventions.getStackArgumentsSize(calleeId) == 8,
          "external stack size did not override persistent evidence");

    const std::uint64_t equalSnapshotRevision = conventions.revision();
    conventions.beginExternalUpdate();
    conventions.setExternalConvention(calleeId, &external);
    conventions.setExternalStackArgumentsSize(
        calleeId, boost::optional<ByteSize>(8));
    conventions.finishExternalUpdate();
    check(conventions.revision() == equalSnapshotRevision,
          "equal convention snapshot advanced the semantic revision");
    check(conventions.getExternalConvention(calleeId) == &external,
          "equal convention snapshot lost stable metadata identity");

    conventions.beginExternalUpdate();
    conventions.setExternalConvention(calleeId, &discarded);
    conventions.setExternalStackArgumentsSize(
        calleeId, boost::optional<ByteSize>(16));
    conventions.cancelExternalUpdate();
    check(conventions.revision() == equalSnapshotRevision,
          "cancelled convention snapshot advanced the revision");
    check(conventions.getExternalConvention(calleeId) == &external &&
              conventions.getExternalStackArgumentsSize(calleeId) &&
              *conventions.getExternalStackArgumentsSize(calleeId) == 8,
          "cancelled convention snapshot was not rolled back atomically");

    conventions.beginExternalUpdate();
    conventions.setExternalConvention(calleeId, &external);
    conventions.setExternalStackArgumentsSize(calleeId, boost::none);
    conventions.finishExternalUpdate();
    const std::uint64_t unknownSizeRevision = conventions.revision();
    check(unknownSizeRevision == equalSnapshotRevision + 1,
          "authoritative unknown stack size did not change the snapshot");
    check(conventions.hasExternalStackArgumentsSizeBinding(calleeId) &&
              !conventions.getExternalStackArgumentsSize(calleeId) &&
              !conventions.getStackArgumentsSize(calleeId),
          "authoritative unknown stack size did not mask persistent evidence");

    conventions.beginExternalUpdate();
    conventions.setExternalConvention(calleeId, &external);
    conventions.setExternalStackArgumentsSize(calleeId, boost::none);
    conventions.finishExternalUpdate();
    check(conventions.revision() == unknownSizeRevision,
          "equal unknown-size binding advanced the semantic revision");

    conventions.beginExternalUpdate();
    conventions.finishExternalUpdate();
    check(conventions.revision() == unknownSizeRevision + 1,
          "omitted external convention facts did not change the snapshot");
    check(!conventions.getExternalConvention(calleeId) &&
              !conventions.hasExternalStackArgumentsSizeBinding(calleeId),
          "stale external convention facts survived replacement");
    check(conventions.getConvention(calleeId) == &fallback &&
              conventions.isFallbackConvention(calleeId),
          "removing metadata did not reveal the persistent fallback");
    check(conventions.getStackArgumentsSize(calleeId) &&
              *conventions.getStackArgumentsSize(calleeId) == 4,
          "removing metadata did not reveal persistent stack evidence");
}

void testExternalRegistriesCancelTogether() {
    Context context;
    ThrowingExternalAnalyzer analyzer;
    bool threw = false;
    try {
        analyzer.decompile(context);
    } catch (const std::runtime_error &) {
        threw = true;
    }

    check(threw, "failing metadata provider did not propagate its error");
    const ir::calling::CalleeId calleeId(
        ir::calling::CallAddress(0x4321));
    check(!context.signatures()->getSignature(
              static_cast<ByteAddr>(0x4321),
              ir::calling::SignatureSource::EXTERNAL),
          "failed metadata pass committed a partial signature snapshot");
    check(!context.conventions()->getExternalConvention(calleeId) &&
              !context.conventions()->hasExternalStackArgumentsSizeBinding(
                  calleeId),
          "failed metadata pass committed a partial convention snapshot");
    check(context.signatures()->revision() == 0 &&
              context.conventions()->revision() == 0,
          "rolling back external registries advanced semantic revisions");
}

void testFailedArmedRefinementRestoresPristineProgram() {
    Context context;
    ThrowingArmedRefinementAnalyzer analyzer;
    bool threw = false;
    try {
        analyzer.decompile(context);
    } catch (const std::runtime_error &) {
        threw = true;
    }

    check(threw, "armed refinement failure did not propagate");
    check(context.program() != nullptr &&
              !context.program()->isFunctionEntry(0x5151),
          "a failed armed refinement exposed a partially mutated Program");
    check(context.functions() == nullptr &&
              context.conventions() == nullptr &&
              context.hooks() == nullptr &&
              context.signatures() == nullptr &&
              context.dataflows() == nullptr &&
              context.livenesses() == nullptr,
          "a failed armed refinement retained products from the old Program");
}

void testExternalContractsReachSemanticFixedPoint() {
    Context context;
    SemanticRefinementAnalyzer analyzer(false);

    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 1,
          "semantic refinement unnecessarily rebuilt functions");
    check(analyzer.signaturePasses() == 2,
          "external contract did not trigger exactly one semantic rerun");
    check(analyzer.dataflowPasses() == 2,
          "dataflow was not recomputed under the external contract");
    check(analyzer.applications() == 2,
          "semantic stability was not verified after contract application");
}

void testConventionOnlyContractsReachSemanticFixedPoint() {
    Context context;
    ConventionRefinementAnalyzer analyzer(false);

    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 1,
          "convention-only refinement unnecessarily rebuilt functions");
    check(analyzer.signaturePasses() == 2 &&
              analyzer.dataflowPasses() == 2,
          "convention-only change did not trigger one semantic rerun");
    check(analyzer.applications() == 2,
          "convention-only stability was not verified");
}

void testConventionSnapshotRemovesUnreproducedFacts() {
    Context context;
    ConventionRefinementAnalyzer analyzer(true);

    analyzer.decompile(context);

    check(analyzer.signaturePasses() == 3 &&
              analyzer.dataflowPasses() == 3 &&
              analyzer.applications() == 3,
          "stale convention removal did not reach a semantic fixed point");
    const ir::calling::CalleeId calleeId(
        ir::calling::CallAddress(0x1234));
    check(!context.conventions()->getExternalConvention(calleeId) &&
              !context.conventions()->hasExternalStackArgumentsSizeBinding(
                  calleeId),
          "one-shot external convention facts remained after evidence vanished");
}

void testSemanticRefinementLimitEndsWithFrozenDataflow() {
    Context context;
    SemanticRefinementAnalyzer analyzer(true);

    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 2,
          "signature oscillation did not rebuild pristine conservative IR");
    check(analyzer.signaturePasses() == 18,
          "bounded refinement omitted the external-free confirmation pass");
    check(analyzer.applications() == 17,
          "bounded refinement applied metadata after the final producer pass");
    check(analyzer.dataflowPasses() == 18,
          "bounded refinement omitted its final frozen dataflow pass");
    check(analyzer.livenessPasses() == 19,
          "frozen dataflow was not paired with refreshed liveness");
    check(!context.signatures()->getSignature(
              static_cast<ByteAddr>(0x1000),
              ir::calling::SignatureSource::EXTERNAL),
          "the arbitrary last side of an oscillation survived the bound");
}

void testCancellationDuringSemanticFallbackInvalidatesOldProducts() {
    Context context;
    CancelingSemanticLimitAnalyzer analyzer;
    bool canceled = false;
    try {
        analyzer.decompile(context);
    } catch (const CancellationException &) {
        canceled = true;
    }

    check(canceled,
          "semantic fallback fixture did not cancel after Program rebuild");
    check(context.program() == nullptr,
          "canceled semantic fallback exposed an incompletely accepted Program");
    check(context.functions() == nullptr &&
              context.conventions() == nullptr &&
              context.hooks() == nullptr &&
              context.signatures() == nullptr &&
              context.dataflows() == nullptr &&
              context.livenesses() == nullptr,
          "canceled semantic fallback retained pointers into the old Program");
}

void testCancellationAfterDataflowRefreshDropsPreviousConsumers() {
    Context context;
    CancelingAfterDataflowRefreshAnalyzer analyzer;
    bool canceled = false;
    try {
        analyzer.decompile(context);
    } catch (const CancellationException &) {
        canceled = true;
    }

    check(canceled,
          "semantic refresh fixture did not cancel before liveness");
    check(context.dataflows() != nullptr,
          "completed refreshed dataflow was discarded unexpectedly");
    check(context.livenesses() == nullptr &&
              context.variables() == nullptr &&
              context.graphs() == nullptr &&
              context.idioms() == nullptr &&
              context.types() == nullptr &&
              context.tree() == nullptr,
          "semantic refresh exposed consumers of a destroyed dataflow pass");
}

void testFailedFunctionDataflowRemovesCapturingHooks() {
    TestArchitecture architecture;
    RegisterAbiConvention convention(
        "test-cdecl", std::vector<std::vector<ir::MemoryLocation>>());
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);

    Context context;
    context.setImage(image);
    MasterAnalyzer analyzer;
    analyzer.createHooks(context);
    context.setDataflows(std::unique_ptr<ir::dflow::Dataflows>(
        new ir::dflow::Dataflows()));

    ir::Function function;
    std::unique_ptr<ir::BasicBlock> block(new ir::BasicBlock());
    ir::BasicBlock *entry = block.get();
    std::unique_ptr<ir::Statement> throwingStatement(new ir::Callback([](){
        throw std::runtime_error("dataflow callback failure");
    }));
    ir::Statement *originalStatement = throwingStatement.get();
    entry->pushBack(std::move(throwingStatement));
    function.addBasicBlock(std::move(block));
    function.setEntry(entry);
    context.conventions()->setConvention(
        ir::calling::getCalleeId(&function), &convention);

    bool threw = false;
    try {
        analyzer.dataflowAnalysis(context, &function);
    } catch (const std::runtime_error &) {
        threw = true;
    }
    check(threw, "function dataflow fixture did not propagate its failure");

    std::size_t statementCount = 0;
    bool retainedOriginal = false;
    foreach (const ir::Statement *statement, entry->statements()) {
        ++statementCount;
        retainedOriginal = retainedOriginal || statement == originalStatement;
    }
    check(statementCount == 1 && retainedOriginal,
          "failed function dataflow retained a hook with a dead Dataflow pointer");
    check(context.dataflows()->empty(),
          "failed function dataflow published a partial result");
}

void installDataflowConsumerSentinels(Context &context) {
    context.setLivenesses(std::unique_ptr<ir::liveness::Livenesses>(
        new ir::liveness::Livenesses()));
    context.setVariables(std::unique_ptr<ir::vars::Variables>(
        new ir::vars::Variables()));
    context.setGraphs(std::unique_ptr<ir::cflow::Graphs>(
        new ir::cflow::Graphs()));
    context.setIdioms(std::unique_ptr<ir::idiom::Idioms>(
        new ir::idiom::Idioms()));
    context.setTypes(std::unique_ptr<ir::types::Types>(
        new ir::types::Types()));
    context.setTree(std::unique_ptr<likec::Tree>(new likec::Tree()));
}

bool dataflowConsumersAreAbsent(const Context &context) {
    return context.livenesses() == nullptr &&
        context.variables() == nullptr &&
        context.graphs() == nullptr &&
        context.idioms() == nullptr &&
        context.types() == nullptr &&
        context.tree() == nullptr;
}

bool dataflowProductsAreAbsent(const Context &context) {
    return context.dataflows() == nullptr &&
        dataflowConsumersAreAbsent(context);
}

void testRepeatedFunctionDataflowReplacesResultAndCallbacks() {
    TestArchitecture architecture;
    RegisterAbiConvention convention(
        "test-cdecl", std::vector<std::vector<ir::MemoryLocation>>());
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);

    Context context;
    context.setImage(image);
    MasterAnalyzer analyzer;
    analyzer.createHooks(context);

    ir::Function function;
    ir::BasicBlock *entry = addSemanticBlock(function);
    function.setEntry(entry);
    ir::Statement *original = entry->pushBack(
        std::unique_ptr<ir::Statement>(new ir::Halt()));
    context.conventions()->setConvention(
        ir::calling::getCalleeId(&function), &convention);

    analyzer.dataflowAnalysis(context, &function);
    check(context.dataflows() && context.dataflows()->size() == 1 &&
              context.dataflows()->at(&function)->converged(),
          "the first per-function dataflow pass was not published");
    const ir::dflow::Dataflow *first =
        context.dataflows()->at(&function).get();
    check(entry->statements().size() > 1,
          "the first per-function pass left no managed callback");
    installDataflowConsumerSentinels(context);

    analyzer.dataflowAnalysis(context, &function);
    check(context.dataflows() && context.dataflows()->size() == 1 &&
              context.dataflows()->at(&function)->converged() &&
              context.dataflows()->at(&function).get() != first,
          "a repeated per-function pass did not replace its old Dataflow");
    check(dataflowConsumersAreAbsent(context),
          "a repeated per-function pass retained stale downstream consumers");
    check(entry->statements().size() > 1,
          "a repeated per-function pass lost its live managed callback");

    context.hooks()->deinstrument(&function);
    check(entry->statements().size() == 1 &&
              entry->statements().front() == original,
          "per-function Dataflow replacement left stale hook statements");
}

void testFailedFunctionDataflowReplacementDropsOldResultAndCallbacks() {
    TestArchitecture architecture;
    RegisterAbiConvention convention(
        "test-cdecl", std::vector<std::vector<ir::MemoryLocation>>());
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);

    Context context;
    context.setImage(image);
    MasterAnalyzer analyzer;
    analyzer.createHooks(context);

    ir::Function function;
    ir::BasicBlock *entry = addSemanticBlock(function);
    function.setEntry(entry);
    ir::Statement *original = entry->pushBack(
        std::unique_ptr<ir::Statement>(new ir::Halt()));
    context.conventions()->setConvention(
        ir::calling::getCalleeId(&function), &convention);
    analyzer.dataflowAnalysis(context, &function);

    ir::Statement *throwing = entry->insertBefore(
        original, std::unique_ptr<ir::Statement>(new ir::Callback([](){
            throw std::runtime_error("replacement dataflow callback failure");
        })));
    installDataflowConsumerSentinels(context);

    bool threw = false;
    try {
        analyzer.dataflowAnalysis(context, &function);
    } catch (const std::runtime_error &) {
        threw = true;
    }
    check(threw,
          "the replacement dataflow fixture did not propagate its failure");
    check(context.dataflows() && context.dataflows()->empty(),
          "a failed replacement retained the old or partial Dataflow");
    check(dataflowConsumersAreAbsent(context),
          "a failed replacement retained stale downstream consumers");

    std::size_t statementCount = 0;
    bool retainedOriginal = false;
    bool retainedThrowing = false;
    foreach (const ir::Statement *statement, entry->statements()) {
        ++statementCount;
        retainedOriginal = retainedOriginal || statement == original;
        retainedThrowing = retainedThrowing || statement == throwing;
    }
    check(statementCount == 2 && retainedOriginal && retainedThrowing,
          "a failed replacement retained callbacks capturing a dead Dataflow");

    entry->erase(throwing);
    analyzer.dataflowAnalysis(context, &function);
    check(context.dataflows() && context.dataflows()->size() == 1 &&
              context.dataflows()->at(&function)->converged(),
          "per-function dataflow could not recover after replacement failure");
    context.hooks()->deinstrument(&function);
    check(entry->statements().size() == 1 &&
              entry->statements().front() == original,
          "recovery after replacement failure left stale hook statements");
}

void testRecreatingHooksAfterDataflowRemovesCapturedCallbacks() {
    TestArchitecture architecture;
    RegisterAbiConvention convention(
        "test-cdecl", std::vector<std::vector<ir::MemoryLocation>>());
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);

    Context context;
    context.setImage(image);
    std::unique_ptr<ir::Functions> functions(new ir::Functions());
    std::unique_ptr<ir::Function> functionStorage(new ir::Function());
    ir::Function *function = functionStorage.get();
    ir::BasicBlock *entry = addSemanticBlock(*function);
    function->setEntry(entry);
    ir::Statement *original = entry->pushBack(
        std::unique_ptr<ir::Statement>(new ir::Halt()));
    functions->addFunction(std::move(functionStorage));
    context.setFunctions(std::move(functions));

    MasterAnalyzer analyzer;
    analyzer.createHooks(context);
    context.conventions()->setConvention(
        ir::calling::getCalleeId(function), &convention);
    analyzer.dataflowAnalysis(context);
    check(context.dataflows() && context.dataflows()->size() == 1 &&
              context.dataflows()->at(function)->converged(),
          "the first public dataflow phase did not publish one result");
    check(entry->statements().size() > 1,
          "the first dataflow pass did not leave its managed callback active");
    installDataflowConsumerSentinels(context);

    analyzer.createHooks(context);
    check(dataflowProductsAreAbsent(context),
          "recreating Hooks retained products referring to the old Dataflow");
    check(entry->statements().size() == 1 &&
              entry->statements().front() == original,
          "recreating Hooks retained a callback capturing the old Dataflow");

    context.conventions()->setConvention(
        ir::calling::getCalleeId(function), &convention);
    analyzer.dataflowAnalysis(context);
    check(context.dataflows() && context.dataflows()->size() == 1 &&
              context.dataflows()->at(function)->converged(),
          "dataflow could not be rerun after Hooks recreation");

    analyzer.createHooks(context);
    check(dataflowProductsAreAbsent(context) &&
              entry->statements().size() == 1 &&
              entry->statements().front() == original,
          "the rerun left a stale callback or pointer-keyed product");
}

void testRecreatingFunctionsDropsPointerKeyedProducts() {
    TestArchitecture architecture;
    RegisterAbiConvention convention(
        "test-cdecl", std::vector<std::vector<ir::MemoryLocation>>());
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);

    Context context;
    context.setImage(image);
    std::unique_ptr<ir::Program> program(new ir::Program());
    ir::BasicBlock *programEntry = program->createBasicBlock(0x3000);
    programEntry->pushBack(
        std::unique_ptr<ir::Statement>(new ir::Halt()));
    program->addFunctionEntry(0x3000);
    context.setProgram(std::move(program));

    MasterAnalyzer analyzer;
    analyzer.createFunctions(context);
    check(context.functions() && context.functions()->list().size() == 1,
          "the function-recreation fixture produced no initial function");
    ir::Function *oldFunction = context.functions()->list().front();
    analyzer.createHooks(context);
    context.conventions()->setConvention(
        ir::calling::getCalleeId(oldFunction), &convention);
    analyzer.dataflowAnalysis(context);
    installDataflowConsumerSentinels(context);

    analyzer.createFunctions(context);
    check(context.functions() && context.functions()->list().size() == 1,
          "recreating Functions lost the Program's function");
    ir::Function *newFunction = context.functions()->list().front();
    check(newFunction != oldFunction && newFunction->entry() &&
              newFunction->entry()->statements().size() == 1 &&
              newFunction->entry()->statements().front()->as<ir::Halt>(),
          "recreating Functions retained an instrumented old clone");
    check(context.hooks() == nullptr &&
              context.signatures() == nullptr &&
              context.conventions() == nullptr &&
              dataflowProductsAreAbsent(context),
          "recreating Functions retained pointer-keyed analysis products");
}

void testRecreatingProgramDropsAllDerivedProducts() {
    const ByteAddr entryAddress = 0x5000;
    TestArchitecture architecture;
    RegisterAbiConvention convention(
        "test-cdecl", std::vector<std::vector<ir::MemoryLocation>>());
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->setEntryPoint(entryAddress);
    auto instructions = std::make_shared<nc::core::arch::Instructions>();
    instructions->add(std::make_shared<TestInstruction>(entryAddress));

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    MasterAnalyzer analyzer;
    analyzer.createProgram(context);
    ir::BasicBlock *programEntry =
        context.program()->getBasicBlockStartingAt(entryAddress);
    check(programEntry != nullptr,
          "the Program-recreation fixture produced no entry block");
    programEntry->pushBack(
        std::unique_ptr<ir::Statement>(new ir::Halt()));
    analyzer.createFunctions(context);
    check(context.functions() && context.functions()->list().size() == 1,
          "the Program-recreation fixture produced no initial function");
    ir::Function *function = context.functions()->list().front();
    analyzer.createHooks(context);
    context.conventions()->setConvention(
        ir::calling::getCalleeId(function), &convention);
    analyzer.dataflowAnalysis(context);
    installDataflowConsumerSentinels(context);

    analyzer.createProgram(context);
    check(context.program() &&
              context.program()->isFunctionEntry(entryAddress),
          "recreating Program lost the authoritative entry boundary");
    check(context.functions() == nullptr &&
              context.hooks() == nullptr &&
              context.signatures() == nullptr &&
              context.conventions() == nullptr &&
              dataflowProductsAreAbsent(context),
          "recreating Program retained products derived from the old IR");
}

void testExternalSnapshotRemovesUnreproducedContracts() {
    Context context;
    SemanticRefinementAnalyzer analyzer(false, true);

    analyzer.decompile(context);

    check(analyzer.signaturePasses() == 3,
          "external contract removal did not reach a semantic fixed point");
    check(analyzer.dataflowPasses() == 3,
          "dataflow was not recomputed after external contract removal");
    check(analyzer.applications() == 3,
          "external snapshot stability was not verified after removal");
    check(!context.signatures()->getSignature(
              static_cast<ByteAddr>(0x1000),
              ir::calling::SignatureSource::EXTERNAL),
          "one-shot external contract remained after its evidence vanished");
}

void testRefinementRebuildsEveryPointerKeyedProduct() {
    Context context;
    RefinementAnalyzer analyzer(2, false);

    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 3,
          "two refinements must cause two complete function rebuilds");
    check(analyzer.signaturePasses() == 5,
          "each Program mutation was not preceded by a stable confirmation pass");
    check(analyzer.dataflowPasses() == 5,
          "Program refinement did not revalidate converged dataflow");
    check(analyzer.acceptedRefinements() == 2,
          "stable metadata refinement accepted the wrong number of entries");
    const auto &permissions = analyzer.refinementPermissions();
    check(permissions.size() == 5,
          "Program refinements did not use dry-run/confirmation pairs");
    check(!permissions[0] && permissions[1] &&
          !permissions[2] && permissions[3] && !permissions[4],
          "Program mutation permission was not gated by stable dry passes");
}

void testRefinementLimitHasNonMutatingFinalIteration() {
    Context context;
    RefinementAnalyzer analyzer(0, true);

    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 17,
          "the refinement bound must cover sixteen nested callbacks");
    check(analyzer.signaturePasses() == 33,
          "bounded refinements omitted semantic confirmation passes");
    check(analyzer.dataflowPasses() == 33,
          "bounded refinement ran an unexpected number of dataflow passes");
    check(analyzer.acceptedRefinements() == 16,
          "the non-mutating final iteration accepted another refinement");

    const auto &permissions = analyzer.refinementPermissions();
    check(permissions.size() == 33,
          "the refinement cap did not produce one final inspection");
    for (std::size_t index = 0; index + 1 < permissions.size(); ++index) {
        check(permissions[index] == (index % 2 == 1),
              "bounded refinements did not alternate dry and armed passes");
    }
    check(!permissions.back(),
          "only the final bounded iteration may prohibit mutation");
}

void testAuthoritativeCallSiteAbisRemainIsolated() {
    const ConstantValue sharedTarget = 0x9000;
    const ir::MemoryLocation ecx =
        nc::arch::x86::X86Registers::ecx()->memoryLocation();
    const ir::MemoryLocation edx =
        nc::arch::x86::X86Registers::edx()->memoryLocation();

    RegisterAbiConvention callerConvention(
        "caller", std::vector<std::vector<ir::MemoryLocation>>());
    RegisterAbiConvention targetConvention(
        "resolved-target",
        std::vector<std::vector<ir::MemoryLocation>>{ {ecx, edx} });
    RegisterAbiConvention thiscallConvention(
        "thiscall32",
        std::vector<std::vector<ir::MemoryLocation>>{ {ecx} });
    RegisterAbiConvention alternateConvention(
        "alternate-register-abi",
        std::vector<std::vector<ir::MemoryLocation>>{ {edx} });

    ir::Function function;
    ir::BasicBlock *block = addSemanticBlock(function);
    function.setEntry(block);
    TestInstruction thiscallInstruction(0x4100);
    TestInstruction alternateInstruction(0x4200);

    addRegisterDefinition(block, ecx, 0x11);
    ir::Call *thiscall = addResolvedCall(
        block, &thiscallInstruction, sharedTarget);
    addRegisterDefinition(block, edx, 0x22);
    ir::Call *alternate = addResolvedCall(
        block, &alternateInstruction, sharedTarget);
    block->pushBack(std::unique_ptr<ir::Statement>(new ir::Halt()));

    ir::calling::Conventions conventions;
    conventions.setConvention(
        ir::calling::CalleeId(&function), &callerConvention);
    conventions.setConvention(
        ir::calling::CalleeId(
            ir::calling::EntryAddress(sharedTarget)),
        &targetConvention);
    conventions.setExternalConvention(
        ir::calling::CalleeId(
            ir::calling::CallAddress(thiscallInstruction.addr())),
        &thiscallConvention);
    conventions.setExternalConvention(
        ir::calling::CalleeId(
            ir::calling::CallAddress(alternateInstruction.addr())),
        &alternateConvention);

    ir::calling::Signatures signatures;
    ir::calling::Hooks hooks(conventions, signatures);
    TestArchitecture architecture;
    runSignatureSemanticPass(
        function, architecture, hooks, signatures);

    check(hasRegisterArguments(
              signatures.getSignature(
                  thiscall,
                  ir::calling::SignatureSource::INFERRED),
              std::vector<ir::MemoryLocation>{ecx}),
          "the authoritative thiscall site did not infer its ECX argument");
    check(hasRegisterArguments(
              signatures.getSignature(
                  alternate,
                  ir::calling::SignatureSource::INFERRED),
              std::vector<ir::MemoryLocation>{edx}),
          "calls sharing a target merged distinct authoritative ABIs");
    check(!signatures.getSignature(
              static_cast<ByteAddr>(sharedTarget),
              ir::calling::SignatureSource::INFERRED),
          "call-site ABI evidence leaked into the shared resolved target");
}

std::shared_ptr<const ir::calling::FunctionPrototype>
makeVariadicRegisterPrototype() {
    std::vector<ir::calling::ParameterDescription> parameters;
    parameters.push_back(ir::calling::ParameterDescription(
        QString("fixed"),
        ir::calling::TypeDescription(
            ir::calling::TypeDescription::POINTER, 32, true),
        ir::calling::ParameterDescription::PointeeAccess::NONE));
    return std::shared_ptr<const ir::calling::FunctionPrototype>(
        new ir::calling::FunctionPrototype(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false),
            parameters, QString(), QString(), true, QString(), true));
}

void publishVariadicCallContract(
        ir::calling::Signatures &signatures, const ir::Call *call,
        const ir::MemoryLocation &fixedArgument,
        const std::shared_ptr<const ir::calling::FunctionPrototype>
            &prototype) {
    std::shared_ptr<ir::calling::CallSignature> external(
        new ir::calling::CallSignature());
    external->arguments().push_back(
        std::shared_ptr<const ir::Term>(
            new ir::MemoryLocationAccess(fixedArgument)));

    const auto &inferred = signatures.getSignature(
        call, ir::calling::SignatureSource::INFERRED);
    if (inferred &&
        (inferred->argumentEvidence() ==
             ir::calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL ||
         inferred->arguments().size() > external->arguments().size()))
    {
        auto firstTrailing = inferred->arguments().begin();
        if (inferred->argumentEvidence() !=
                ir::calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL)
        {
            firstTrailing += external->arguments().size();
        }
        external->arguments().insert(
            external->arguments().end(), firstTrailing,
            inferred->arguments().end());
    }
    external->setPrototype(prototype);

    signatures.beginExternalUpdate();
    try {
        signatures.setSignature(
            call, external,
            ir::calling::SignatureSource::EXTERNAL);
        signatures.finishExternalUpdate();
    } catch (...) {
        signatures.cancelExternalUpdate();
        throw;
    }
}

void testVariadicTailIsRevalidatedAcrossSemanticPasses() {
    const ConstantValue target = 0xa000;
    const ir::MemoryLocation fixedRegister(
        ir::MemoryDomain::FIRST_REGISTER + 72, 0, 32);
    const ir::MemoryLocation trailingRegister(
        ir::MemoryDomain::FIRST_REGISTER + 73, 0, 32);

    RegisterAbiConvention callerConvention(
        "caller", std::vector<std::vector<ir::MemoryLocation>>());
    /* Separate argument classes make a trailing observation independently
     * sortable after the authoritative fixed prefix has been consumed by its
     * synthetic call read. This is representative of ABIs with independent
     * integer/vector register banks, rather than a fixture-specific opcode. */
    RegisterAbiConvention variadicConvention(
        "variadic-register-abi",
        std::vector<std::vector<ir::MemoryLocation>>{
            {fixedRegister}, {trailingRegister}
        });

    ir::Function function;
    ir::BasicBlock *block = addSemanticBlock(function);
    function.setEntry(block);
    TestInstruction callInstruction(0x4300);
    addRegisterDefinition(block, fixedRegister, 0x31);
    ir::Statement *trailingDefinition =
        addRegisterDefinition(block, trailingRegister, 0x32);
    ir::Call *call = addResolvedCall(
        block, &callInstruction, target);
    block->pushBack(std::unique_ptr<ir::Statement>(new ir::Halt()));

    ir::calling::Conventions conventions;
    conventions.setConvention(
        ir::calling::CalleeId(&function), &callerConvention);
    conventions.setExternalConvention(
        ir::calling::CalleeId(
            ir::calling::CallAddress(callInstruction.addr())),
        &variadicConvention);
    ir::calling::Signatures signatures;
    ir::calling::Hooks hooks(conventions, signatures);
    TestArchitecture architecture;
    const auto prototype = makeVariadicRegisterPrototype();

    runSignatureSemanticPass(
        function, architecture, hooks, signatures);
    check(hasRegisterArguments(
              signatures.getSignature(
                  call, ir::calling::SignatureSource::INFERRED),
              std::vector<ir::MemoryLocation>{
                  fixedRegister, trailingRegister}),
          "the initial pass did not observe the fixed and trailing arguments");
    publishVariadicCallContract(
        signatures, call, fixedRegister, prototype);
    check(hasRegisterArguments(
              signatures.getSignature(call),
              std::vector<ir::MemoryLocation>{
                  fixedRegister, trailingRegister}),
          "external publication discarded the initial variadic tail");

    runSignatureSemanticPass(
        function, architecture, hooks, signatures);
    const auto &secondInference = signatures.getSignature(
        call, ir::calling::SignatureSource::INFERRED);
    check(hasRegisterArguments(
              secondInference,
              std::vector<ir::MemoryLocation>{trailingRegister}) &&
              secondInference->argumentEvidence() ==
                  ir::calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL,
          "the second pass did not revalidate only the variadic tail");
    publishVariadicCallContract(
        signatures, call, fixedRegister, prototype);
    check(hasRegisterArguments(
              signatures.getSignature(call),
              std::vector<ir::MemoryLocation>{
                  fixedRegister, trailingRegister}),
          "a revalidated variadic tail did not survive a second semantic pass");

    block->erase(trailingDefinition);
    runSignatureSemanticPass(
        function, architecture, hooks, signatures);
    const auto &vanishedInference = signatures.getSignature(
        call, ir::calling::SignatureSource::INFERRED);
    check(vanishedInference && vanishedInference->arguments().empty() &&
              vanishedInference->argumentEvidence() ==
                  ir::calling::CallSignature::ArgumentEvidence::VARIADIC_TAIL,
          "stale variadic-tail evidence survived after its definition vanished");
    publishVariadicCallContract(
        signatures, call, fixedRegister, prototype);
    check(hasRegisterArguments(
              signatures.getSignature(call),
              std::vector<ir::MemoryLocation>{fixedRegister}),
          "external refinement retained a stale variadic argument");

    /* Verify that the fixed-only state is stable and does not recreate the
     * removed tail merely because the old hook once read it. */
    runSignatureSemanticPass(
        function, architecture, hooks, signatures);
    publishVariadicCallContract(
        signatures, call, fixedRegister, prototype);
    check(hasRegisterArguments(
              signatures.getSignature(call),
              std::vector<ir::MemoryLocation>{fixedRegister}),
          "a removed variadic tail became self-sustaining on a later pass");
}

} // anonymous namespace

int main() {
    try {
        testFunctionSymbolsSeedProgramBoundaries();
        testExternalTransactionsUseCommittedReadSnapshot();
        testSignatureProvenancePreservesBothLayers();
        testConventionProvenanceUsesReplacementSnapshots();
        testExternalRegistriesCancelTogether();
        testFailedArmedRefinementRestoresPristineProgram();
        testExternalContractsReachSemanticFixedPoint();
        testConventionOnlyContractsReachSemanticFixedPoint();
        testConventionSnapshotRemovesUnreproducedFacts();
        testSemanticRefinementLimitEndsWithFrozenDataflow();
        testCancellationDuringSemanticFallbackInvalidatesOldProducts();
        testCancellationAfterDataflowRefreshDropsPreviousConsumers();
        testFailedFunctionDataflowRemovesCapturingHooks();
        testRepeatedFunctionDataflowReplacesResultAndCallbacks();
        testFailedFunctionDataflowReplacementDropsOldResultAndCallbacks();
        testRecreatingHooksAfterDataflowRemovesCapturedCallbacks();
        testRecreatingFunctionsDropsPointerKeyedProducts();
        testRecreatingProgramDropsAllDerivedProducts();
        testExternalSnapshotRemovesUnreproducedContracts();
        testRefinementRebuildsEveryPointerKeyedProduct();
        testRefinementLimitHasNonMutatingFinalIteration();
        testAuthoritativeCallSiteAbisRemainIsolated();
        testVariadicTailIsRevalidatedAcrossSemanticPasses();
    } catch (const std::exception &exception) {
        std::cerr << exception.what() << '\n';
        return 1;
    }
    return 0;
}
