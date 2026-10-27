/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <vector>

#include <boost/none.hpp>
#include <boost/optional.hpp>

#include <QByteArray>
#include <QString>

#include <nc/common/Foreach.h>
#include <nc/core/Context.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/arch/Instructions.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Section.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/calling/CalleeId.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/calling/SymbolPrototypeRegistry.h>

#include <nc/arch/x86/X86Architecture.h>
#include <nc/arch/x86/X86MasterAnalyzer.h>

using namespace nc;
using namespace nc::core;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

ir::Call *findCall(ir::Program &program, ByteAddr instructionAddress) {
    ir::Call *result = nullptr;
    foreach (auto basicBlock, program.basicBlocks()) {
        foreach (auto statement, basicBlock->statements()) {
            auto call = statement->as<ir::Call>();
            if (call && call->instruction() &&
                call->instruction()->addr() == instructionAddress)
            {
                check(!result,
                      "fixture contains duplicate Program calls at one address");
                result = call;
            }
        }
    }
    return result;
}

const ir::Call *findCall(
        const ir::Functions &functions, ByteAddr instructionAddress) {
    const ir::Call *result = nullptr;
    foreach (const auto function, functions.list()) {
        foreach (const auto basicBlock, function->basicBlocks()) {
            foreach (const auto statement, basicBlock->statements()) {
                const auto call = statement->asCall();
                if (call && call->instruction() &&
                    call->instruction()->addr() == instructionAddress)
                {
                    check(!result,
                          "fixture contains overlapping final call clones");
                    result = call;
                }
            }
        }
    }
    return result;
}

bool haltImmediatelyFollows(const ir::Call *call) {
    if (!call || !call->basicBlock()) {
        return false;
    }
    const auto basicBlock = call->basicBlock();
    auto position = basicBlock->statements().get_iterator(call);
    ++position;
    if (position == basicBlock->statements().end() ||
        !(*position)->is<ir::Halt>())
    {
        return false;
    }
    ++position;
    return position == basicBlock->statements().end();
}

bool hasHaltWithoutSameInstructionPostCall(const ir::Call *call) {
    if (!call || !call->basicBlock()) {
        return false;
    }
    const auto basicBlock = call->basicBlock();
    auto position = basicBlock->statements().get_iterator(call);
    ++position;
    for (; position != basicBlock->statements().end(); ++position) {
        const auto statement = *position;
        if (statement->instruction() == call->instruction()) {
            return false;
        }
    }
    const auto terminator = basicBlock->getTerminator();
    return terminator && terminator->is<ir::Halt>();
}

class TrackingAnalyzer: public nc::arch::x86::X86MasterAnalyzer {
    const ByteAddr callAddress_;
    const ByteAddr continuationAddress_;
    const bool expectRefinement_;
    const bool probeDisabledRefinement_;
    mutable unsigned int functionBuilds_;
    mutable unsigned int acceptedRefinements_;
    mutable unsigned int externalApplications_;
    mutable bool checkedDisabledRefinement_;

    void checkInitialFallthrough(Context &context) const {
        auto program = context.program();
        auto call = findCall(*program, callAddress_);
        check(call != nullptr, "fixture Program call is missing");
        const auto jump = call->basicBlock()->getJump();
        check(jump && !jump->instruction() && jump->isUnconditional(),
              "indirect call did not retain its synthetic fallthrough");
        check(jump->thenTarget().basicBlock() ==
                  program->getBasicBlockStartingAt(continuationAddress_),
              "indirect call fallthrough targets the wrong continuation");
    }

public:
    TrackingAnalyzer(ByteAddr callAddress, ByteAddr continuationAddress,
                     bool expectRefinement = true,
                     bool probeDisabledRefinement = true):
        callAddress_(callAddress),
        continuationAddress_(continuationAddress),
        expectRefinement_(expectRefinement),
        probeDisabledRefinement_(probeDisabledRefinement), functionBuilds_(0),
        acceptedRefinements_(0), externalApplications_(0),
        checkedDisabledRefinement_(false)
    {}

    unsigned int functionBuilds() const { return functionBuilds_; }
    unsigned int acceptedRefinements() const {
        return acceptedRefinements_;
    }
    unsigned int externalApplications() const {
        return externalApplications_;
    }
    bool checkedDisabledRefinement() const {
        return checkedDisabledRefinement_;
    }

    void createProgram(Context &context) const override {
        X86MasterAnalyzer::createProgram(context);
        checkInitialFallthrough(context);
    }

    void createFunctions(Context &context) const override {
        ++functionBuilds_;
        X86MasterAnalyzer::createFunctions(context);
    }

    bool applyExternalSignatures(
            Context &context, bool allowProgramRefinement) const override {
        ++externalApplications_;
        if (probeDisabledRefinement_ && !checkedDisabledRefinement_) {
            auto call = findCall(*context.program(), callAddress_);
            auto block = call ? call->basicBlock() : nullptr;
            auto jump = block ? block->getJump() : nullptr;
            check(X86MasterAnalyzer::applyExternalSignatures(
                      context, false) == expectRefinement_,
                  expectRefinement_ ?
                      "disabled noreturn refinement was not reported" :
                      "ambiguous noreturn evidence requested refinement");
            check(call && call->basicBlock() == block &&
                      block->getJump() == jump &&
                      block->getTerminator() &&
                      !block->getTerminator()->is<ir::Halt>(),
                  "disabled noreturn refinement mutated Program CFG");
            checkedDisabledRefinement_ = true;
        }

        const bool result =
            X86MasterAnalyzer::applyExternalSignatures(
                context, allowProgramRefinement);
        if (result && allowProgramRefinement) {
            ++acceptedRefinements_;
        }
        return result;
    }

    void reconstructVariables(Context &) const override {}
    void structuralAnalysis(Context &) const override {}
    void analyzeIdioms(Context &) const override {}
    void reconstructTypes(Context &) const override {}
    void generateTree(Context &) const override {}
};

class BoundaryInstruction: public nc::core::arch::Instruction {
public:
    explicit BoundaryInstruction(ByteAddr address):
        nc::core::arch::Instruction(address, 1)
    {}

    void print(QTextStream &) const override {}
};

class BoundaryAddressAnalyzer:
    public nc::arch::x86::X86MasterAnalyzer {
    const ByteAddr originalCallAddress_;
    const BoundaryInstruction boundaryInstruction_;
    mutable unsigned int functionBuilds_;
    mutable unsigned int externalApplications_;
    mutable unsigned int requestedRefinements_;

public:
    BoundaryAddressAnalyzer(
            ByteAddr originalCallAddress, ByteAddr boundaryAddress):
        originalCallAddress_(originalCallAddress),
        boundaryInstruction_(boundaryAddress), functionBuilds_(0),
        externalApplications_(0), requestedRefinements_(0)
    {}

    unsigned int functionBuilds() const { return functionBuilds_; }
    unsigned int externalApplications() const {
        return externalApplications_;
    }
    unsigned int requestedRefinements() const {
        return requestedRefinements_;
    }

    void createProgram(Context &context) const override {
        X86MasterAnalyzer::createProgram(context);
        ir::Call *original = findCall(
            *context.program(), originalCallAddress_);
        check(original != nullptr && original->basicBlock() != nullptr,
              "boundary fixture Program call is missing");
        ir::BasicBlock *block = original->basicBlock();
        const auto position = block->statements().get_iterator(original);
        std::unique_ptr<ir::Call> replacement(new ir::Call(
            original->target()->clone()));
        replacement->setInstruction(&boundaryInstruction_);
        block->insert(position, std::move(replacement));
        block->erase(original);
    }

    void createFunctions(Context &context) const override {
        ++functionBuilds_;
        X86MasterAnalyzer::createFunctions(context);
    }

    bool applyExternalSignatures(
            Context &context, bool allowProgramRefinement) const override {
        ++externalApplications_;
        const bool result = X86MasterAnalyzer::applyExternalSignatures(
            context, allowProgramRefinement);
        if (result) {
            ++requestedRefinements_;
        }
        return result;
    }

    void reconstructVariables(Context &) const override {}
    void structuralAnalysis(Context &) const override {}
    void analyzeIdioms(Context &) const override {}
    void reconstructTypes(Context &) const override {}
    void generateTree(Context &) const override {}
};

std::size_t countFunctionCallsAt(
        const ir::Functions &functions, ByteAddr instructionAddress) {
    std::size_t result = 0;
    foreach (const auto function, functions.list()) {
        foreach (const auto basicBlock, function->basicBlocks()) {
            foreach (const auto statement, basicBlock->statements()) {
                const auto call = statement->asCall();
                if (call && call->instruction() &&
                    call->instruction()->addr() == instructionAddress)
                {
                    ++result;
                }
            }
        }
    }
    return result;
}

void runDirectExternalContractFixture(
        image::ExternalNameOrigin origin, const QString &symbolName,
        const QString &moduleName,
        const std::shared_ptr<const ir::calling::FunctionPrototype>
            &prototype,
        const QString &recordConvention,
        const boost::optional<ByteSize> &recordStackArgumentsSize,
        bool recordDoesNotReturn, bool expectContract,
        const QString &expectedConvention,
        const boost::optional<ByteSize> &expectedStackArgumentsSize,
        bool expectSignature, bool expectRefinement,
        const char *fixtureDescription) {
    const ByteAddr codeAddress = 0x3000;
    const ByteAddr callAddress = codeAddress;
    const ByteAddr continuationAddress = codeAddress + 5;
    const ByteAddr externalAddress = 0x9000;

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(continuationAddress);

    /* rel32 = externalAddress - (codeAddress + sizeof(call rel32)). */
    const char code[] =
        "\xe8\xfb\x5f\x00\x00"
        "\xb8\x2a\x00\x00\x00"
        "\xc3";
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("direct_external_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    image->addSymbol(std::unique_ptr<image::Symbol>(new image::Symbol(
        image::SymbolType::FUNCTION, symbolName, externalAddress,
        nullptr, moduleName, origin)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "direct external fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(callAddress) != nullptr,
          "direct external fixture call did not disassemble");

    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    if (prototype) {
        check(registry->add(
                  moduleName, symbolName,
                  ir::calling::SymbolPrototypeRecord(
                      prototype, recordConvention,
                      recordStackArgumentsSize, recordDoesNotReturn),
                  1, QString("direct_external_provider")) ==
                  ir::calling::SymbolPrototypeRegistry::ADDED,
              "direct external fixture record was not added");
    }

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(
        callAddress, continuationAddress, expectRefinement);
    analyzer.decompile(context);

    check(analyzer.checkedDisabledRefinement(), fixtureDescription);
    check(analyzer.functionBuilds() ==
              (expectRefinement ? 2U : 1U) &&
              analyzer.acceptedRefinements() ==
                  (expectRefinement ? 1U : 0U),
          "direct external fixture applied the wrong CFG refinement");

    const ir::calling::CalleeId callSiteId{
        ir::calling::CallAddress(callAddress)};
    const auto externalConvention =
        context.conventions()->getExternalConvention(callSiteId);
    if (expectContract) {
        check(externalConvention ==
                  architecture.getCallingConvention(expectedConvention) &&
                  context.conventions()->
                      hasExternalStackArgumentsSizeBinding(callSiteId) &&
                  context.conventions()->getExternalStackArgumentsSize(
                      callSiteId) == expectedStackArgumentsSize,
              "direct external fixture lost its ABI contract");
    } else {
        check(!externalConvention &&
                  !context.conventions()->
                      hasExternalStackArgumentsSizeBinding(callSiteId),
              "untrusted or incompatible external metadata published an ABI contract");
    }

    const ir::Call *functionCall = findCall(
        *context.functions(), callAddress);
    check(functionCall != nullptr,
          "direct external fixture lost its final call clone");
    check(static_cast<bool>(context.signatures()->getSignature(
              functionCall,
              ir::calling::SignatureSource::EXTERNAL)) ==
              expectSignature,
          "direct external fixture published the wrong signature layer");

    ir::Call *programCall = findCall(*context.program(), callAddress);
    check(programCall != nullptr &&
              haltImmediatelyFollows(programCall) == expectRefinement,
          "direct external fixture applied the wrong noreturn effect");
}

void testDataflowProvedNoReturnRefinesProgram() {
    const ByteAddr codeAddress = 0x1000;
    const ByteAddr callAddress = 0x1007;
    const ByteAddr continuationAddress = 0x1009;
    const ByteAddr importSlot = 0x3000;
    const QString moduleName("fixture_runtime");
    const QString symbolName("fixture_terminate");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);

    const char code[] =
        "\x75\x07"                  /* jne continuation */
        "\xa1\x00\x30\x00\x00"  /* mov eax, [importSlot] */
        "\xff\xd0"                  /* call eax */
        "\xb8\x2a\x00\x00\x00"  /* mov eax, 42 */
        "\xc3";                     /* ret */
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("fixture_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto importSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, symbolName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(importSlot, importSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "fixture disassembler produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(callAddress) != nullptr,
          "fixture call instruction did not disassemble");

    const auto prototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")));
    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, symbolName,
              ir::calling::SymbolPrototypeRecord(
                  prototype, QString("cdecl32"),
                  boost::optional<ByteSize>(0), true),
              1, QString("fixture_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "fixture noreturn contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(callAddress, continuationAddress);
    analyzer.decompile(context);

    check(analyzer.checkedDisabledRefinement(),
          "non-mutating refinement mode was not exercised");
    check(analyzer.functionBuilds() == 2,
          "noreturn CFG refinement did not cause exactly one outer rebuild");
    check(analyzer.acceptedRefinements() == 1,
          "noreturn CFG refinement was not idempotent");

    auto programCall = findCall(*context.program(), callAddress);
    check(haltImmediatelyFollows(programCall),
          "Program retained post-call effects before noreturn Halt");
    check(ir::CFG(context.program()->basicBlocks()).
              getSuccessors(programCall->basicBlock()).empty(),
          "Program retained the noreturn call's fallthrough edge");

    auto continuation = context.program()->getBasicBlockStartingAt(
        continuationAddress);
    check(continuation != nullptr,
          "noreturn refinement lost the continuation block");
    check(ir::CFG(context.program()->basicBlocks()).
              getPredecessors(continuation).size() == 1,
          "noreturn refinement removed a different branch's continuation edge");

    const auto functionCall = findCall(*context.functions(), callAddress);
    check(hasHaltWithoutSameInstructionPostCall(functionCall),
          "final Function clone retained a machine post-call effect");
    check(ir::CFG(functionCall->basicBlock()->function()->basicBlocks()).
              getSuccessors(functionCall->basicBlock()).empty(),
          "final Function clone retained stale noreturn fallthrough");
}

void testOverwrittenDirectImportDoesNotRefineProgram() {
    const ByteAddr codeAddress = 0x1800;
    const ByteAddr callAddress = 0x180a;
    const ByteAddr continuationAddress = 0x1810;
    const ByteAddr importSlot = 0x3800;
    const QString moduleName("mutable_runtime");
    const QString symbolName("declared_terminate");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(continuationAddress);

    /* The relocation declares a noreturn import, but this path overwrites the
     * slot before the direct memory call. Static import metadata must not
     * delete a fallthrough which belongs to the replacement target. */
    const char code[] =
        "\xc7\x05\x00\x38\x00\x00\x00\x50\x00\x00"
        "\xff\x15\x00\x38\x00\x00"
        "\xb8\x2a\x00\x00\x00"
        "\xc3";
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("mutable_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto importSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, symbolName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(importSlot, importSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "mutable fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(callAddress) != nullptr,
          "mutable direct call instruction did not disassemble");

    const auto prototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")));
    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, symbolName,
              ir::calling::SymbolPrototypeRecord(
                  prototype, QString("stdcall32"),
                  boost::optional<ByteSize>(0), true),
              1, QString("mutable_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "mutable fixture noreturn contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(callAddress, continuationAddress, false);
    analyzer.decompile(context);

    check(analyzer.checkedDisabledRefinement(),
          "mutable fixture did not exercise non-mutating mode");
    check(analyzer.functionBuilds() == 1,
          "an overwritten import slot unexpectedly rebuilt Functions");
    check(analyzer.acceptedRefinements() == 0,
          "an overwritten import slot was accepted as noreturn");

    auto programCall = findCall(*context.program(), callAddress);
    check(programCall != nullptr,
          "an overwritten import slot deleted the Program call");
    const auto jump = programCall->basicBlock()->getJump();
    check(jump && !jump->instruction() && jump->isUnconditional() &&
              jump->thenTarget().basicBlock() ==
                  context.program()->getBasicBlockStartingAt(
                      continuationAddress),
          "an overwritten import slot pruned the Program fallthrough");
    const ir::calling::CalleeId callSiteId{
        ir::calling::CallAddress(callAddress)};
    check(!context.conventions()->getExternalConvention(callSiteId) &&
              !context.conventions()->
                  hasExternalStackArgumentsSizeBinding(callSiteId),
          "an overwritten import slot retained an external ABI contract");
    check(context.conventions()->isFallbackConvention(callSiteId) &&
              context.conventions()->getConvention(callSiteId) ==
                  architecture.getCallingConvention(QString("cdecl32")),
          "an overwritten import slot promoted metadata during provisional dataflow");
    const auto finalCall = findCall(*context.functions(), callAddress);
    check(finalCall && !context.signatures()->getSignature(
              finalCall, ir::calling::SignatureSource::EXTERNAL),
          "an overwritten import slot retained an external call signature");
}

void testCrossFunctionImportPatchRejectsExternalContract() {
    const ByteAddr codeAddress = 0x3000;
    const ByteAddr patcherAddress = 0x3020;
    const ByteAddr callAddress = 0x3005;
    const ByteAddr continuationAddress = 0x300b;
    const ByteAddr importSlot = 0x6000;
    const QString moduleName("global_mutable_runtime");
    const QString symbolName("declared_global_terminate");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(patcherAddress);
    image->addFunctionEntry(continuationAddress);

    /* The caller itself never writes the slot. A different recovered
     * function does, and is called first. Per-function reaching definitions
     * alone cannot turn the relocation into a program-wide invariant. */
    const char code[] =
        "\xe8\x1b\x00\x00\x00"      /* call patcher */
        "\xff\x15\x00\x60\x00\x00"  /* call [importSlot] */
        "\xb8\x2a\x00\x00\x00"      /* continuation */
        "\xc3"
        "\x90\x90\x90\x90\x90\x90\x90\x90"
        "\x90\x90\x90\x90\x90\x90\x90"
        "\xc7\x05\x00\x60\x00\x00\x00\x50\x00\x00"
        "\xc3";                         /* patcher: slot = 0x5000; ret */
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("global_mutable_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto importSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, symbolName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(importSlot, importSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "global mutable fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(callAddress) != nullptr &&
              instructions->get(patcherAddress) != nullptr,
          "global mutable fixture did not disassemble");

    const auto prototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")));
    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, symbolName,
              ir::calling::SymbolPrototypeRecord(
                  prototype, QString("stdcall32"),
                  boost::optional<ByteSize>(0), true),
              1, QString("global_mutable_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "global mutable contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(callAddress, continuationAddress, false);
    analyzer.decompile(context);

    check(analyzer.checkedDisabledRefinement(),
          "global mutable fixture did not exercise non-mutating mode");
    check(analyzer.functionBuilds() == 1 &&
              analyzer.acceptedRefinements() == 0,
          "a cross-function import patch was accepted as noreturn");
    const ir::calling::CalleeId callSiteId{
        ir::calling::CallAddress(callAddress)};
    check(!context.conventions()->getExternalConvention(callSiteId) &&
              !context.conventions()->
                  hasExternalStackArgumentsSizeBinding(callSiteId),
          "a cross-function import patch retained an external ABI contract");
    const auto finalCall = findCall(*context.functions(), callAddress);
    check(finalCall && !context.signatures()->getSignature(
              finalCall, ir::calling::SignatureSource::EXTERNAL),
          "a cross-function import patch retained an external signature");

    auto programCall = findCall(*context.program(), callAddress);
    check(programCall != nullptr,
          "a cross-function import patch deleted the Program call");
    const auto jump = programCall->basicBlock()->getJump();
    check(jump && !jump->instruction() && jump->isUnconditional() &&
              jump->thenTarget().basicBlock() ==
                  context.program()->getBasicBlockStartingAt(
                      continuationAddress),
          "a cross-function import patch pruned the Program fallthrough");
}

void testCallbackBoundaryRestartPrecedesNoReturnRefinement() {
    const ByteAddr codeAddress = 0x2800;
    const ByteAddr registrarCallAddress = 0x2805;
    const ByteAddr callbackAddress = 0x2817;
    const ByteAddr callAddress = 0x2819;
    const ByteAddr continuationAddress = 0x281b;
    const ByteAddr registrarSlot = 0x4800;
    const ByteAddr noReturnSlot = 0x5000;
    const QString moduleName("callback_runtime");
    const QString registrarName("register_callback");
    const QString noReturnName("terminate_from_callback");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(continuationAddress);

    /* The original owner proves eax came from the noreturn IAT slot before
     * reaching the shared call. The registrar contract discovers a second
     * entry which also reaches that call, but without the original owner's
     * eax definition. Noreturn pruning must therefore wait for the boundary
     * rebuild and reject the mixed proof/unknown evidence. */
    const char code[] =
        "\x68\x17\x28\x00\x00"  /* push callbackAddress */
        "\xff\x15\x00\x48\x00\x00" /* call [registrarSlot] */
        "\x83\xc4\x04"              /* add esp, 4 */
        "\xa1\x00\x50\x00\x00"  /* mov eax, [noReturnSlot] */
        "\x85\xc0"                  /* test eax, eax */
        "\x75\x02"                  /* jne sharedCall */
        "\xeb\x00"                  /* callbackAddress: jmp sharedCall */
        "\xff\xd0"                  /* sharedCall: call eax */
        "\xb8\x2a\x00\x00\x00"  /* continuation */
        "\xc3";                     /* ret */
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("callback_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto registrarSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, registrarName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(registrarSlot, registrarSymbol, 4)));
    const auto noReturnSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, noReturnName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(noReturnSlot, noReturnSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "callback fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(registrarCallAddress) != nullptr,
          "callback registrar call did not disassemble");
    check(instructions->get(callAddress) != nullptr,
          "callback-owned noreturn call did not disassemble");
    check(image->functionEntries().count(callbackAddress) == 0,
          "callback fixture accidentally seeded the callback entry");

    const auto callbackPrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")),
            std::vector<ir::calling::ParameterDescription>(),
            QString("__cdecl"), QString("fixture_callback"), true,
            QString("cdecl32"), false);
    std::vector<ir::calling::ParameterDescription> registrarParameters;
    registrarParameters.push_back(ir::calling::ParameterDescription(
        QString("callback"),
        ir::calling::TypeDescription(
            ir::calling::TypeDescription::POINTER, 32, true,
            QString("fixture_callback_t")),
        /* Exercise a non-stack writable-pointer effect. It is a synthetic
         * callee-memory summary, not evidence that decoded code patched an
         * unrelated import slot, and must not make contracts oscillate. */
        ir::calling::ParameterDescription::PointeeAccess::READ_WRITE,
        callbackPrototype));
    const auto registrarPrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")),
            std::move(registrarParameters), QString(), QString(), true);
    const auto noReturnPrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")));

    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, registrarName,
              ir::calling::SymbolPrototypeRecord(
                  registrarPrototype, QString("cdecl32"),
                  boost::optional<ByteSize>(4), false),
              1, QString("callback_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "callback registrar contract was not authoritative");
    check(registry->add(
              moduleName, noReturnName,
              ir::calling::SymbolPrototypeRecord(
                  noReturnPrototype, QString("cdecl32"),
                  boost::optional<ByteSize>(0), true),
              1, QString("callback_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "callback noreturn contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(
        callAddress, continuationAddress, true, false);
    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 2,
          "callback boundary did not cause exactly one outer rebuild");
    check(analyzer.acceptedRefinements() == 1,
          "callback boundary refinement was not idempotent");
    check(analyzer.externalApplications() < 16,
          "callback external contracts oscillated to the refinement bound");
    check(context.program()->isFunctionEntry(callbackAddress),
          "callback metadata did not refine the Program function entry");
    check(countFunctionCallsAt(*context.functions(), callAddress) == 2,
          "callback boundary did not produce both call owners");

    const ir::Function *callbackFunction = nullptr;
    foreach (const auto function, context.functions()->list()) {
        if (function->entry() && function->entry()->address() &&
            *function->entry()->address() == callbackAddress)
        {
            callbackFunction = function;
            break;
        }
    }
    check(callbackFunction != nullptr,
          "callback boundary did not produce a callback Function");
    const auto callbackSignature = context.signatures()->getSignature(
        callbackFunction, ir::calling::SignatureSource::EXTERNAL);
    check(callbackSignature && callbackSignature->prototype(),
          "callback contract was not retained at the semantic fixed point");
    check(callbackSignature->prototype()->abiConventionName() ==
              QString("cdecl32"),
          "callback ABI was not retained at the semantic fixed point");
    const ir::calling::CalleeId callbackId{
        ir::calling::EntryAddress(callbackAddress)};
    check(context.conventions()->getExternalConvention(callbackId) ==
              architecture.getCallingConvention(QString("cdecl32")),
          "callback calling convention was not retained");
    check(context.conventions()->hasExternalStackArgumentsSizeBinding(
              callbackId) &&
              context.conventions()->getExternalStackArgumentsSize(
                  callbackId) == boost::optional<ByteSize>(0),
          "callback stack extent was not retained");

    auto programCall = findCall(*context.program(), callAddress);
    check(programCall != nullptr,
          "stale noreturn evidence deleted the shared Program call");
    const auto jump = programCall->basicBlock()->getJump();
    check(jump && !jump->instruction() && jump->isUnconditional() &&
              jump->thenTarget().basicBlock() ==
                  context.program()->getBasicBlockStartingAt(
                      continuationAddress),
          "stale noreturn evidence pruned the shared call fallthrough");
}

void testUnknownOverlappingCloneRejectsNoReturnRefinement() {
    const ByteAddr codeAddress = 0x2000;
    const ByteAddr secondEntryAddress = 0x2007;
    const ByteAddr callAddress = 0x2010;
    const ByteAddr continuationAddress = 0x2012;
    const ByteAddr importSlot = 0x4000;
    const QString moduleName("overlap_runtime");
    const QString symbolName("overlap_terminate");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(secondEntryAddress);
    image->addFunctionEntry(continuationAddress);

    /* The first entry defines eax from the IAT; the second entry reaches the
     * same Program call with eax undefined. FunctionsGenerator clones the
     * shared call into both Functions, so one proof plus one unknown must not
     * prune the Program edge. */
    const char code[] =
        "\xa1\x00\x40\x00\x00"  /* mov eax, [importSlot] */
        "\xeb\x09"                  /* jmp sharedCall */
        "\xeb\x07"                  /* second entry: jmp sharedCall */
        "\x90\x90\x90\x90\x90\x90\x90"
        "\xff\xd0"                  /* sharedCall: call eax */
        "\xb8\x2a\x00\x00\x00"  /* continuation */
        "\xc3";
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("overlap_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto importSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, symbolName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(importSlot, importSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "overlap fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(callAddress) != nullptr,
          "overlap call instruction did not disassemble");

    const auto prototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")));
    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, symbolName,
              ir::calling::SymbolPrototypeRecord(
                  prototype, QString("cdecl32"),
                  boost::optional<ByteSize>(0), true),
              1, QString("overlap_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "overlap noreturn contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(
        callAddress, continuationAddress, false);
    analyzer.decompile(context);

    check(analyzer.checkedDisabledRefinement(),
          "overlap fixture did not exercise non-mutating mode");
    check(analyzer.functionBuilds() == 1,
          "ambiguous clone evidence unexpectedly rebuilt Functions");
    check(analyzer.acceptedRefinements() == 0,
          "ambiguous clone evidence was accepted");
    check(countFunctionCallsAt(*context.functions(), callAddress) == 2,
          "overlap fixture did not produce two Function call clones");

    const ir::calling::CalleeId callSiteId{
        ir::calling::CallAddress(callAddress)};
    check(!context.conventions()->getExternalConvention(callSiteId) &&
              !context.conventions()->
                  hasExternalStackArgumentsSizeBinding(callSiteId),
          "one proved clone leaked an ABI contract to an ambiguous call site");
    foreach (const auto function, context.functions()->list()) {
        foreach (const auto basicBlock, function->basicBlocks()) {
            foreach (const auto statement, basicBlock->statements()) {
                const auto call = statement->asCall();
                if (call && call->instruction() &&
                    call->instruction()->addr() == callAddress)
                {
                    check(!context.signatures()->getSignature(
                              call, ir::calling::SignatureSource::EXTERNAL),
                          "one proved clone leaked a signature to an "
                          "ambiguous call site");
                }
            }
        }
    }

    auto programCall = findCall(*context.program(), callAddress);
    check(programCall != nullptr,
          "ambiguous clone evidence deleted the Program call");
    const auto jump = programCall->basicBlock()->getJump();
    check(jump && !jump->instruction() && jump->isUnconditional() &&
              jump->thenTarget().basicBlock() ==
                  context.program()->getBasicBlockStartingAt(
                      continuationAddress),
          "ambiguous clone evidence pruned the Program fallthrough");
}

void testUnknownOverlappingCloneRejectsCallbackBoundary() {
    const ByteAddr codeAddress = 0x2a00;
    const ByteAddr secondEntryAddress = 0x2a07;
    const ByteAddr registrarCallAddress = 0x2a10;
    const ByteAddr continuationAddress = 0x2a16;
    const ByteAddr callbackAddress = 0x2a18;
    const ByteAddr registrarSlot = 0x4a00;
    const QString moduleName("callback_consensus_runtime");
    const QString registrarName("indirect_registrar");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(secondEntryAddress);
    image->addFunctionEntry(continuationAddress);

    /* Both entries own a clone of the same registrar call. Only the first
     * owner defines the register argument as a concrete code address; the
     * second reaches it as incoming state. A callback boundary is global
     * Program state, so one local proof cannot be allowed to create it. */
    const char code[] =
        "\xb9\x18\x2a\x00\x00"  /* mov ecx, callbackAddress */
        "\xeb\x09"                  /* jmp sharedRegistrarCall */
        "\xeb\x07"                  /* second entry: jmp shared call */
        "\x90\x90\x90\x90\x90\x90\x90"
        "\xff\x15\x00\x4a\x00\x00" /* call [registrarSlot] */
        "\xc3"                      /* continuation */
        "\x90"
        "\xc3";                     /* callback candidate */
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("callback_consensus_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto registrarSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, registrarName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(registrarSlot, registrarSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "callback consensus fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(registrarCallAddress) != nullptr &&
              instructions->get(callbackAddress) != nullptr,
          "callback consensus fixture did not disassemble its boundaries");
    check(image->functionEntries().count(callbackAddress) == 0,
          "callback consensus fixture pre-seeded the candidate boundary");

    const auto callbackPrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false),
            std::vector<ir::calling::ParameterDescription>(),
            QString(), QString(), true, QString("cdecl32"), false);
    std::vector<ir::calling::ParameterDescription> parameters;
    parameters.push_back(ir::calling::ParameterDescription(
        QString("callback"),
        ir::calling::TypeDescription(
            ir::calling::TypeDescription::POINTER, 32, true),
        ir::calling::ParameterDescription::PointeeAccess::NONE,
        callbackPrototype));
    const auto registrarPrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false),
            std::move(parameters), QString(), QString(), true);

    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, registrarName,
              ir::calling::SymbolPrototypeRecord(
                  registrarPrototype, QString("thiscall32"),
                  boost::optional<ByteSize>(0), false),
              1, QString("callback_consensus_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "callback consensus registrar contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(
        registrarCallAddress, continuationAddress, false, false);
    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 1 &&
              analyzer.acceptedRefinements() == 0,
          "one callback proof unexpectedly refined global Program state");
    check(analyzer.externalApplications() < 16,
          "ambiguous callback evidence oscillated to the refinement bound");
    check(countFunctionCallsAt(
              *context.functions(), registrarCallAddress) == 2,
          "callback consensus fixture did not create two call clones");

    const ir::calling::CalleeId callSiteId{
        ir::calling::CallAddress(registrarCallAddress)};
    check(context.conventions()->getExternalConvention(callSiteId) ==
              architecture.getCallingConvention(QString("thiscall32")) &&
              context.conventions()->getExternalStackArgumentsSize(
                  callSiteId) == boost::optional<ByteSize>(0),
          "clone consensus rejected the registrar contract itself");

    check(!context.program()->isFunctionEntry(callbackAddress),
          "one clone's callback argument created a global function boundary");
    const ir::calling::CalleeId callbackId{
        ir::calling::EntryAddress(callbackAddress)};
    check(!context.conventions()->getExternalConvention(callbackId) &&
              !context.signatures()->getSignature(
                  callbackAddress,
                  ir::calling::SignatureSource::EXTERNAL),
          "one clone leaked a callback ABI or signature");
    foreach (const auto function, context.functions()->list()) {
        if (function->entry() && function->entry()->address() &&
            *function->entry()->address() == callbackAddress)
        {
            /* FunctionsGenerator may represent an otherwise-unowned decoded
             * component without promoting it into Program boundary state. */
            check(!context.signatures()->getSignature(
                      function,
                      ir::calling::SignatureSource::EXTERNAL),
                  "one clone leaked a callback Function signature");
        }
    }
}

void runUnrepresentableContinuationFixture(ByteAddr boundaryAddress) {
    const ByteAddr codeAddress = 0x2c00;
    const ByteAddr originalCallAddress = codeAddress;
    const ByteAddr continuationAddress = codeAddress + 6;
    const ByteAddr importSlot = 0x4c00;
    const QString moduleName("boundary_runtime");
    const QString symbolName("terminating_target");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(continuationAddress);

    const char code[] =
        "\xff\x15\x00\x4c\x00\x00" /* call [importSlot] */
        "\xb8\x2a\x00\x00\x00"
        "\xc3";
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("boundary_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto importSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, symbolName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(importSlot, importSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "boundary fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(originalCallAddress) != nullptr,
          "boundary fixture call did not disassemble");

    const auto prototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false));
    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, symbolName,
              ir::calling::SymbolPrototypeRecord(
                  prototype, QString("cdecl32"),
                  boost::optional<ByteSize>(0), true),
              1, QString("boundary_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED,
          "boundary noreturn contract was not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    BoundaryAddressAnalyzer analyzer(
        originalCallAddress, boundaryAddress);
    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 1 &&
              analyzer.externalApplications() > 0 &&
              analyzer.requestedRefinements() == 0,
          "an unrepresentable continuation requested CFG refinement");
    ir::Call *programCall = findCall(*context.program(), boundaryAddress);
    check(programCall != nullptr && !haltImmediatelyFollows(programCall),
          "an unrepresentable continuation was destructively terminated");
    check(context.program()->getBasicBlockCovering(
              (std::numeric_limits<ByteAddr>::max)()) == nullptr,
          "the maximum address was treated as a representable half-open range");
}

void testNoReturnContinuationAddressBounds() {
    const ByteAddr maximum =
        (std::numeric_limits<ByteAddr>::max)();
    runUnrepresentableContinuationFixture(maximum - 1);
    runUnrepresentableContinuationFixture(maximum);
}

std::shared_ptr<const ir::calling::FunctionPrototype>
makeVoidPrototype() {
    return std::make_shared<const ir::calling::FunctionPrototype>(
        ir::calling::TypeDescription(
            ir::calling::TypeDescription::VOID, 0, false,
            QString("void")));
}

std::shared_ptr<const ir::calling::FunctionPrototype>
makeSharedX86CallbackDag(unsigned int depth, std::size_t fanout) {
    const ir::calling::TypeDescription voidType(
        ir::calling::TypeDescription::VOID, 0, false, QString("void"));
    std::shared_ptr<const ir::calling::FunctionPrototype> child =
        std::make_shared<const ir::calling::FunctionPrototype>(
            voidType, std::vector<ir::calling::ParameterDescription>(),
            QString(), QString(), true, QString("cdecl32"), false);

    for (unsigned int level = 0; level < depth; ++level) {
        std::vector<ir::calling::ParameterDescription> parameters;
        parameters.reserve(fanout);
        for (std::size_t index = 0; index < fanout; ++index) {
            parameters.push_back(ir::calling::ParameterDescription(
                QString("callback"),
                ir::calling::TypeDescription(
                    ir::calling::TypeDescription::POINTER, 32, true,
                    QString("callback_t")),
                ir::calling::ParameterDescription::PointeeAccess::NONE,
                child));
        }
        child = std::make_shared<const ir::calling::FunctionPrototype>(
            voidType, std::move(parameters), QString(), QString(), true,
            QString("cdecl32"), false);
    }
    return child;
}

void testStructurallyEqualSharedCallbackDagsMergeOnce() {
    const ByteAddr codeAddress = 0x2e00;
    const ByteAddr firstCallAddress = 0x2e05;
    const ByteAddr secondCallAddress = 0x2e13;
    const ByteAddr secondContinuationAddress = 0x2e19;
    const ByteAddr callbackAddress = 0x2e20;
    const ByteAddr firstRegistrarSlot = 0x4e00;
    const ByteAddr secondRegistrarSlot = 0x4e04;
    const QString moduleName("callback_dag_runtime");
    const QString firstRegistrarName("register_first_dag");
    const QString secondRegistrarName("register_second_dag");

    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    auto image = std::make_shared<image::Image>();
    image->platform().setArchitecture(&architecture);
    image->platform().setOperatingSystem(image::Platform::Windows);
    image->setEntryPoint(codeAddress);
    image->addFunctionEntry(secondContinuationAddress);

    const char code[] =
        "\x68\x20\x2e\x00\x00"      /* push callbackAddress */
        "\xff\x15\x00\x4e\x00\x00"  /* call [firstRegistrarSlot] */
        "\x83\xc4\x04"                  /* add esp, 4 */
        "\x68\x20\x2e\x00\x00"      /* push callbackAddress */
        "\xff\x15\x04\x4e\x00\x00"  /* call [secondRegistrarSlot] */
        "\x83\xc4\x04"                  /* add esp, 4 */
        "\xc3"                              /* caller ret */
        "\x90\x90\x90"
        "\xc3";                             /* callback candidate */
    std::unique_ptr<image::Section> codeSection(new image::Section(
        QString("callback_dag_code"), codeAddress,
        static_cast<ByteSize>(sizeof(code) - 1)));
    codeSection->setAllocated();
    codeSection->setReadable();
    codeSection->setExecutable();
    codeSection->setCode();
    codeSection->setContent(QByteArray(code, sizeof(code) - 1));
    const image::Section *codeSource = codeSection.get();
    image->addSection(std::move(codeSection));

    const auto firstSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, firstRegistrarName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(firstRegistrarSlot, firstSymbol, 4)));
    const auto secondSymbol = image->addSymbol(
        std::unique_ptr<image::Symbol>(new image::Symbol(
            image::SymbolType::FUNCTION, secondRegistrarName, boost::none,
            nullptr, moduleName,
            image::ExternalNameOrigin::OBJECT_FILE)));
    image->addRelocation(std::unique_ptr<image::Relocation>(
        new image::Relocation(secondRegistrarSlot, secondSymbol, 4)));

    auto instructions = std::make_shared<core::arch::Instructions>();
    auto disassembler = architecture.createDisassembler();
    CancellationToken canceled;
    disassembler->disassemble(
        image.get(), codeSource, codeAddress,
        codeAddress + sizeof(code) - 1,
        [&](std::shared_ptr<core::arch::Instruction> instruction) {
            check(instructions->add(std::move(instruction)),
                  "callback DAG fixture produced a duplicate instruction");
        },
        canceled);
    check(instructions->get(firstCallAddress) != nullptr &&
              instructions->get(secondCallAddress) != nullptr &&
              instructions->get(callbackAddress) != nullptr,
          "callback DAG fixture did not disassemble its boundaries");
    check(image->functionEntries().count(callbackAddress) == 0,
          "callback DAG fixture pre-seeded the callback entry");

    auto makeRegistrarPrototype = [](
            std::shared_ptr<const ir::calling::FunctionPrototype> callback) {
        std::vector<ir::calling::ParameterDescription> parameters;
        parameters.push_back(ir::calling::ParameterDescription(
            QString("callback"),
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::POINTER, 32, true,
                QString("callback_t")),
            ir::calling::ParameterDescription::PointeeAccess::NONE,
            std::move(callback)));
        return std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")),
            std::move(parameters), QString(), QString(), true);
    };

    /* The two roots are separately allocated but structurally equal. Within
     * each root, every level shares one child, so pair-wise merging must
     * traverse 16 prototype pairs rather than the 6^15 expanded paths. */
    const auto firstPrototype = makeRegistrarPrototype(
        makeSharedX86CallbackDag(15, 6));
    const auto secondPrototype = makeRegistrarPrototype(
        makeSharedX86CallbackDag(15, 6));
    check(firstPrototype->parameters()[0].callbackPrototype() !=
              secondPrototype->parameters()[0].callbackPrototype(),
          "callback DAG fixture accidentally reused both roots");

    std::unique_ptr<ir::calling::SymbolPrototypeRegistry> registry(
        new ir::calling::SymbolPrototypeRegistry());
    check(registry->add(
              moduleName, firstRegistrarName,
              ir::calling::SymbolPrototypeRecord(
                  firstPrototype, QString("cdecl32"),
                  boost::optional<ByteSize>(4), false),
              1, QString("callback_dag_provider")) ==
              ir::calling::SymbolPrototypeRegistry::ADDED &&
              registry->add(
                  moduleName, secondRegistrarName,
                  ir::calling::SymbolPrototypeRecord(
                      secondPrototype, QString("cdecl32"),
                      boost::optional<ByteSize>(4), false),
                  1, QString("callback_dag_provider")) ==
                  ir::calling::SymbolPrototypeRegistry::ADDED,
          "callback DAG registrar contracts were not authoritative");

    Context context;
    context.setImage(image);
    context.setInstructions(instructions);
    context.setSymbolPrototypeRegistry(std::move(registry));

    TrackingAnalyzer analyzer(
        secondCallAddress, secondContinuationAddress, true, false);
    analyzer.decompile(context);

    check(analyzer.functionBuilds() == 2 &&
              analyzer.acceptedRefinements() == 1 &&
              analyzer.externalApplications() < 16,
          "shared callback DAG merge did not reach a bounded fixed point");
    check(context.program()->isFunctionEntry(callbackAddress),
          "equal callback DAGs did not refine their shared callback entry");
    const ir::calling::CalleeId callbackId{
        ir::calling::EntryAddress(callbackAddress)};
    check(context.conventions()->getExternalConvention(callbackId) ==
              architecture.getCallingConvention(QString("cdecl32")) &&
              context.signatures()->getSignature(
                  callbackAddress,
                  ir::calling::SignatureSource::EXTERNAL) != nullptr,
          "equal callback DAGs did not publish one callback contract");
}

void testDirectExternalSymbolTrustBoundary() {
    const auto prototype = makeVoidPrototype();

    /* A linker/object-file symbol outside every mapped section is not proof
     * that a direct target is an external process function. In contrast, a
     * debugger-resolved symbol at the same address is an explicit runtime
     * observation and may carry the provider contract. */
    runDirectExternalContractFixture(
        image::ExternalNameOrigin::OBJECT_FILE,
        QString("trusted_terminate"), QString("trust_boundary"),
        prototype, QString("cdecl32"), boost::optional<ByteSize>(0),
        true, false, QString(), boost::none, false, false,
        "object-file direct target did not exercise non-mutating mode");
    runDirectExternalContractFixture(
        image::ExternalNameOrigin::DEBUGGER,
        QString("trusted_terminate"), QString("trust_boundary"),
        prototype, QString("cdecl32"), boost::optional<ByteSize>(0),
        true, true, QString("cdecl32"), boost::optional<ByteSize>(0),
        true, true,
        "debugger direct target did not exercise non-mutating mode");
}

void testDebuggerStdcallDecorationWithoutProvider() {
    /* The ABI encoded by a debugger's exact `_name@N` display survives even
     * when no prototype provider knows the symbol. Module-qualified debugger
     * wrappers must be normalized before interpreting that decoration. */
    runDirectExternalContractFixture(
        image::ExternalNameOrigin::DEBUGGER, QString("_Foo@8"),
        QString("kernel32"),
        std::shared_ptr<const ir::calling::FunctionPrototype>(), QString(),
        boost::none, false, true, QString("stdcall32"),
        boost::optional<ByteSize>(8), false, false,
        "plain decorated debugger target did not exercise non-mutating mode");
    runDirectExternalContractFixture(
        image::ExternalNameOrigin::DEBUGGER,
        QString("<kernel32!_Foo@8>"), QString("kernel32"),
        std::shared_ptr<const ir::calling::FunctionPrototype>(), QString(),
        boost::none, false, true, QString("stdcall32"),
        boost::optional<ByteSize>(8), false, false,
        "wrapped decorated debugger target did not exercise non-mutating mode");

    /* Decoration is only ABI evidence when its cleanup can be represented
     * by the 16-bit immediate of an x86 stdcall RET. */
    runDirectExternalContractFixture(
        image::ExternalNameOrigin::DEBUGGER,
        QString("_Foo@4294967296"), QString("kernel32"),
        std::shared_ptr<const ir::calling::FunctionPrototype>(), QString(),
        boost::none, false, false, QString(), boost::none, false, false,
        "oversized decorated debugger target did not exercise non-mutating mode");
}

void testIncompatibleExternalPrototypeLayoutsAreRejected() {
    std::vector<ir::calling::ParameterDescription> wideParameters;
    wideParameters.push_back(ir::calling::ParameterDescription(
        QString("wide"),
        ir::calling::TypeDescription(
            ir::calling::TypeDescription::INTEGER, 64, false,
            QString("int64_t")),
        ir::calling::ParameterDescription::PointeeAccess::NONE));
    const auto widePrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")),
            std::move(wideParameters), QString(), QString(), true);

    runDirectExternalContractFixture(
        image::ExternalNameOrigin::DEBUGGER, QString("wide_scalar"),
        QString("layout_boundary"), widePrototype, QString("stdcall32"),
        boost::optional<ByteSize>(4), true, false, QString(), boost::none,
        false, false,
        "wide scalar fixture did not exercise non-mutating mode");

    /* Target compatibility is recursive: a pointer-sized callback parameter
     * cannot smuggle a target-incompatible scalar through its nested ABI. */
    const auto incompatibleCallback =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::INTEGER, 64, false,
                QString("int64_t")),
            std::vector<ir::calling::ParameterDescription>(), QString(),
            QString(), true, QString("cdecl32"), false);
    std::vector<ir::calling::ParameterDescription> callbackParameters;
    callbackParameters.push_back(ir::calling::ParameterDescription(
        QString("callback"),
        ir::calling::TypeDescription(
            ir::calling::TypeDescription::POINTER, 32, true,
            QString("callback_t")),
        ir::calling::ParameterDescription::PointeeAccess::NONE,
        incompatibleCallback));
    const auto outerPrototype =
        std::make_shared<const ir::calling::FunctionPrototype>(
            ir::calling::TypeDescription(
                ir::calling::TypeDescription::VOID, 0, false,
                QString("void")),
            std::move(callbackParameters), QString(), QString(), true);

    runDirectExternalContractFixture(
        image::ExternalNameOrigin::DEBUGGER, QString("wide_callback"),
        QString("layout_boundary"), outerPrototype, QString("stdcall32"),
        boost::optional<ByteSize>(4), true, false, QString(), boost::none,
        false, false,
        "nested wide scalar fixture did not exercise non-mutating mode");
}

} // anonymous namespace

int main() {
    try {
        testDataflowProvedNoReturnRefinesProgram();
        testOverwrittenDirectImportDoesNotRefineProgram();
        testCrossFunctionImportPatchRejectsExternalContract();
        testCallbackBoundaryRestartPrecedesNoReturnRefinement();
        testUnknownOverlappingCloneRejectsNoReturnRefinement();
        testUnknownOverlappingCloneRejectsCallbackBoundary();
        testNoReturnContinuationAddressBounds();
        testStructurallyEqualSharedCallbackDagsMergeOnce();
        testDirectExternalSymbolTrustBoundary();
        testDebuggerStdcallDecorationWithoutProvider();
        testIncompatibleExternalPrototypeLayoutsAreRejected();
    } catch (const std::exception &exception) {
        std::cerr << "x86 noreturn refinement regression test failed: "
                  << exception.what() << '\n';
        return 1;
    }
    return 0;
}

/* vim:set et sts=4 sw=4: */
