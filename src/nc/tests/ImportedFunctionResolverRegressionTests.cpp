/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <memory>
#include <stdexcept>
#include <vector>

#include <boost/none.hpp>

#include <QLatin1String>
#include <QString>

#include <nc/common/CancellationToken.h>
#include <nc/common/LogToken.h>
#include <nc/common/SizedValue.h>
#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/ImportedFunctionResolver.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DataflowAnalyzer.h>
#include <nc/core/irgen/InstructionAnalyzer.h>

using namespace nc;
using namespace nc::core;
using namespace nc::core::ir;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

class TestArchitecture: public arch::Architecture {
public:
    explicit TestArchitecture(SmallBitSize bitness = 32) {
        setName(QLatin1String("resolver-test"));
        setBitness(bitness);
        setMaxInstructionSize(16);
    }

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

std::unique_ptr<Term> constant(SmallBitSize size, ConstantValue value) {
    return std::unique_ptr<Term>(
        new Constant(SizedValue(size, value)));
}

std::unique_ptr<Term> importLoad(ByteAddr slot,
                                 SmallBitSize pointerSize = 32) {
    return std::unique_ptr<Term>(new Dereference(
        constant(pointerSize, static_cast<ConstantValue>(slot)),
        MemoryDomain::MEMORY, pointerSize));
}

BasicBlock *addBlock(Function &function) {
    std::unique_ptr<BasicBlock> block(new BasicBlock());
    BasicBlock *result = block.get();
    function.addBasicBlock(std::move(block));
    return result;
}

Term *addDefinition(BasicBlock *block, const MemoryLocation &location,
                    std::unique_ptr<Term> source) {
    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(location));
    Term *result = destination.get();
    block->pushBack(std::unique_ptr<Statement>(new Assignment(
        std::move(destination), std::move(source))));
    return result;
}

Call *addRegisterCall(BasicBlock *block,
                      const MemoryLocation &location) {
    std::unique_ptr<Call> call(new Call(
        std::unique_ptr<Term>(new MemoryLocationAccess(location))));
    Call *result = call.get();
    block->pushBack(std::move(call));
    return result;
}

Call *addDirectMemoryCall(BasicBlock *block, ByteAddr slot,
                          SmallBitSize pointerSize = 32) {
    std::unique_ptr<Call> call(new Call(importLoad(slot, pointerSize)));
    Call *result = call.get();
    block->pushBack(std::move(call));
    return result;
}

std::unique_ptr<ir::dflow::Dataflow> analyze(
        Function &function, const TestArchitecture &architecture) {
    std::unique_ptr<ir::dflow::Dataflow> dataflow(
        new ir::dflow::Dataflow());
    CancellationToken canceled;
    LogToken log;
    ir::dflow::DataflowAnalyzer(
        *dataflow, &architecture, canceled, log).analyze(
            CFG(function.basicBlocks()));
    check(dataflow->converged(),
          "resolver fixture must reach a dataflow fixpoint");
    return dataflow;
}

class ImportTable {
    std::vector<std::unique_ptr<image::Symbol>> symbols_;
    std::vector<std::unique_ptr<image::Relocation>> relocations_;

public:
    const image::Symbol *add(ByteAddr slot, const char *name,
                            ByteSize relocationSize = 4,
                            ByteSize addend = 0,
                            const boost::optional<ConstantValue> &value =
                                boost::none) {
        std::unique_ptr<image::Symbol> symbol(new image::Symbol(
            image::SymbolType::FUNCTION, QLatin1String(name), boost::none,
            nullptr, QLatin1String("resolver-test.dll"),
            image::ExternalNameOrigin::OBJECT_FILE));
        if (value) {
            symbol.reset(new image::Symbol(
                image::SymbolType::FUNCTION, QLatin1String(name), value));
        }
        const image::Symbol *result = symbol.get();
        symbols_.push_back(std::move(symbol));
        relocations_.push_back(std::unique_ptr<image::Relocation>(
            new image::Relocation(
                slot, result, relocationSize, addend)));
        return result;
    }

    const image::Relocation *lookup(ByteAddr slot) const {
        for (const auto &relocation : relocations_) {
            if (relocation->address() == slot) {
                return relocation.get();
            }
        }
        return nullptr;
    }
};

const image::Symbol *resolve(const Call *call,
                             const ir::dflow::Dataflow &dataflow,
                             const ImportTable &imports,
                             SmallBitSize pointerSize = 32) {
    return calling::resolveImportedFunction(
        call, dataflow, pointerSize,
        [&imports](ByteAddr slot) {
            return imports.lookup(slot);
        });
}

void test64BitCopyChain() {
    const ByteAddr slot = 0x100001234LL;
    const MemoryLocation firstRegister(
        MemoryDomain::FIRST_REGISTER + 103, 0, 64);
    const MemoryLocation secondRegister(
        MemoryDomain::FIRST_REGISTER + 104, 0, 64);

    TestArchitecture architecture(64);
    ImportTable imports;
    const image::Symbol *symbol = imports.add(
        slot, "import_wide", 8);

    Function function;
    BasicBlock *block = addBlock(function);
    function.setEntry(block);
    addDefinition(block, firstRegister, importLoad(slot, 64));
    addDefinition(block, secondRegister,
        std::unique_ptr<Term>(new MemoryLocationAccess(firstRegister)));
    Call *call = addRegisterCall(block, secondRegister);
    block->pushBack(std::unique_ptr<Statement>(new Halt()));

    const auto dataflow = analyze(function, architecture);
    check(resolve(call, *dataflow, imports, 64) == symbol,
          "a 64-bit register copy chain must retain its import origin");
    check(resolve(call, *dataflow, imports, 32) == nullptr,
          "the requested pointer width must match the call target");
}

void testDirectLoadAndCopyChain() {
    const ByteAddr slot = 0x5000;
    const MemoryLocation firstRegister(
        MemoryDomain::FIRST_REGISTER + 100, 0, 32);
    const MemoryLocation secondRegister(
        MemoryDomain::FIRST_REGISTER + 101, 0, 32);
    const MemoryLocation thirdRegister(
        MemoryDomain::FIRST_REGISTER + 102, 0, 32);

    TestArchitecture architecture;
    ImportTable imports;
    const image::Symbol *symbol = imports.add(
        slot, "import_alpha");

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == symbol,
              "a direct relocation-backed memory call must resolve");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block, firstRegister, importLoad(slot));
        addDefinition(block, secondRegister,
            std::unique_ptr<Term>(
                new MemoryLocationAccess(firstRegister)));
        addDefinition(block, thirdRegister,
            std::unique_ptr<Term>(
                new MemoryLocationAccess(secondRegister)));
        Call *call = addRegisterCall(block, thirdRegister);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == symbol,
              "an exact register copy chain must retain its import origin");

        dataflow->setConverged(false);
        check(resolve(call, *dataflow, imports) == nullptr,
              "an unfinished dataflow result must never resolve a call");
    }
}

const image::Symbol *analyzeDiamond(
        bool rightDefinesValue, bool useConflictingImport) {
    static TestArchitecture architecture;
    static ImportTable imports;
    static bool initialized = false;
    static const image::Symbol *firstSymbol = nullptr;
    static const image::Symbol *secondSymbol = nullptr;
    const ByteAddr firstSlot = 0x5100;
    const ByteAddr secondSlot = 0x5200;
    const MemoryLocation targetRegister(
        MemoryDomain::FIRST_REGISTER + 110, 0, 32);

    if (!initialized) {
        firstSymbol = imports.add(firstSlot, "import_first");
        secondSymbol = imports.add(secondSlot, "import_second");
        initialized = true;
    }

    Function function;
    BasicBlock *entry = addBlock(function);
    BasicBlock *left = addBlock(function);
    BasicBlock *right = addBlock(function);
    BasicBlock *join = addBlock(function);
    function.setEntry(entry);

    entry->pushBack(std::unique_ptr<Statement>(new Jump(
        constant(1, 1), JumpTarget(left), JumpTarget(right))));
    addDefinition(left, targetRegister, importLoad(firstSlot));
    left->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(join))));
    if (rightDefinesValue) {
        addDefinition(right, targetRegister, importLoad(
            useConflictingImport ? secondSlot : firstSlot));
    }
    right->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(join))));
    Call *call = addRegisterCall(join, targetRegister);
    join->pushBack(std::unique_ptr<Statement>(new Halt()));

    const auto dataflow = analyze(function, architecture);
    const image::Symbol *result = resolve(call, *dataflow, imports);
    if (!useConflictingImport && rightDefinesValue) {
        check(result == firstSymbol,
              "complete alternatives from the same import must merge");
    }
    if (useConflictingImport) {
        check(secondSymbol != nullptr,
              "the conflict fixture must contain a second import");
    }
    return result;
}

void testMergedDefinitionsAndConflicts() {
    check(analyzeDiamond(true, false) != nullptr,
          "equivalent import definitions must resolve");
    check(analyzeDiamond(true, true) == nullptr,
          "different import definitions must fail closed");
    check(analyzeDiamond(false, false) == nullptr,
          "an incoming undefined alternative must fail closed");
}

void testUnknownAndOpaqueClobbers() {
    const ByteAddr slot = 0x5300;
    const MemoryLocation targetRegister(
        MemoryDomain::FIRST_REGISTER + 120, 0, 32);
    TestArchitecture architecture;
    ImportTable imports;
    imports.add(slot, "import_clobber");

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block, targetRegister, importLoad(slot));
        block->pushBack(std::unique_ptr<Statement>(
            new InlineAssembly()));
        Call *call = addRegisterCall(block, targetRegister);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "an opaque clobber must invalidate a prior import origin");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block, targetRegister, importLoad(slot));
        addDefinition(block, targetRegister,
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::UNDEFINED, 32)));
        Call *call = addRegisterCall(block, targetRegister);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "an explicit unknown overwrite must fail closed");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block, targetRegister, importLoad(slot));
        addDefinition(block,
            MemoryLocation(targetRegister.domain(),
                           targetRegister.addr(), 8),
            constant(8, 0));
        Call *call = addRegisterCall(block, targetRegister);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a partial overwrite must invalidate an import origin");
    }
}

void testImportSlotWrites() {
    const ByteAddr slot = 0x5350;
    const BitAddr slotBits = slot * CHAR_BIT;
    const MemoryLocation targetRegister(
        MemoryDomain::FIRST_REGISTER + 121, 0, 32);
    TestArchitecture architecture;
    ImportTable imports;
    const image::Symbol *symbol = imports.add(slot, "import_mutable_slot");

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block,
            MemoryLocation(MemoryDomain::MEMORY, slotBits, 32),
            constant(32, 0));
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a full visible import-slot overwrite must fail closed");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block,
            MemoryLocation(MemoryDomain::MEMORY, slotBits + 8, 8),
            constant(8, 0));
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a partial visible import-slot overwrite must fail closed");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block,
            MemoryLocation(MemoryDomain::MEMORY,
                           (slot + 4) * CHAR_BIT, 32),
            constant(32, 0));
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == symbol,
              "a disjoint global write must not poison an import slot");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block, targetRegister, importLoad(slot));
        addDefinition(block,
            MemoryLocation(MemoryDomain::MEMORY, slotBits, 32),
            constant(32, 0));
        Call *call = addRegisterCall(block, targetRegister);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == symbol,
              "a captured import pointer must survive a later slot write");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        addDefinition(block, targetRegister, importLoad(slot));
        Call *call = addRegisterCall(block, targetRegister);
        addDefinition(block,
            MemoryLocation(MemoryDomain::MEMORY, slotBits, 32),
            constant(32, 0));
        block->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(block))));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a loop-carried slot overwrite must affect later executions");
    }

    {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        block->pushBack(std::unique_ptr<Statement>(new InlineAssembly()));
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));

        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "opaque assembly before an import load must fail closed");
    }
}

void testTrackedMemoryInvalidations() {
    const ByteAddr slot = 0x5380;
    TestArchitecture architecture;
    ImportTable imports;
    const image::Symbol *symbol = imports.add(
        slot, "import_after_effect");

    const auto resolveAfterInvalidation = [&](
            std::unique_ptr<TrackedMemoryInvalidation> invalidation) {
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        block->pushBack(std::move(invalidation));
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));
        const auto dataflow = analyze(function, architecture);
        return resolve(call, *dataflow, imports);
    };

    check(resolveAfterInvalidation(
              std::unique_ptr<TrackedMemoryInvalidation>(
                  new TrackedMemoryInvalidation(
                      TrackedMemoryInvalidation::ALL_TRACKED_MEMORY))) ==
              symbol,
              "synthetic whole-memory effects must not poison static "
              "linkage slots");

    {
        std::vector<std::unique_ptr<Term>> candidates;
        candidates.push_back(constant(32, 0x7000));
        check(resolveAfterInvalidation(
                  std::unique_ptr<TrackedMemoryInvalidation>(
                      new TrackedMemoryInvalidation(
                          std::move(candidates)))) == symbol,
              "a contract-derived pointer effect must not become a decoded "
              "linkage-slot write");
    }

    {
        std::vector<std::unique_ptr<Term>> candidates;
        candidates.push_back(std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::UNKNOWN, 32)));
        check(resolveAfterInvalidation(
                  std::unique_ptr<TrackedMemoryInvalidation>(
                      new TrackedMemoryInvalidation(
                          std::move(candidates)))) == symbol,
              "an unresolved synthetic pointer effect must not make import "
              "proof depend on the current prototype snapshot");
    }

    {
        std::vector<std::unique_ptr<Term>> candidates;
        candidates.push_back(std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::ZERO_STACK_OFFSET, 32)));
        check(resolveAfterInvalidation(
                  std::unique_ptr<TrackedMemoryInvalidation>(
                      new TrackedMemoryInvalidation(
                          std::move(candidates)))) == symbol,
              "an exact frame-relative writable pointer must not poison "
              "disjoint import slots");
    }

    {
        std::vector<std::unique_ptr<Term>> candidates;
        check(resolveAfterInvalidation(
                  std::unique_ptr<TrackedMemoryInvalidation>(
                      new TrackedMemoryInvalidation(
                          std::move(candidates)))) == symbol,
              "a complete no-write effect must preserve import slots");
    }
}

void testRelocationValidation() {
    TestArchitecture architecture;

    {
        const ByteAddr slot = 0x5400;
        ImportTable imports;
        imports.add(slot, "wide_relocation", 8);
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));
        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a relocation with the wrong pointer width must fail");
    }

    {
        const ByteAddr slot = 0x5500;
        ImportTable imports;
        imports.add(slot, "adjusted_relocation", 4, 1);
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));
        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a relocation with a nonzero addend is not an exact import entry");
    }

    {
        const ByteAddr slot = 0x5600;
        ImportTable imports;
        imports.add(
            slot, "local_target", 4, 0,
            boost::optional<ConstantValue>(0x6000));
        Function function;
        BasicBlock *block = addBlock(function);
        function.setEntry(block);
        Call *call = addDirectMemoryCall(block, slot);
        block->pushBack(std::unique_ptr<Statement>(new Halt()));
        const auto dataflow = analyze(function, architecture);
        check(resolve(call, *dataflow, imports) == nullptr,
              "a relocation to a defined local function is not an import");
    }
}

} // anonymous namespace

int main() {
    try {
        testDirectLoadAndCopyChain();
        test64BitCopyChain();
        testMergedDefinitionsAndConflicts();
        testUnknownAndOpaqueClobbers();
        testImportSlotWrites();
        testTrackedMemoryInvalidations();
        testRelocationValidation();
    } catch (const std::exception &exception) {
        std::cerr << "imported function resolver regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }
    return 0;
}

/* vim:set et sts=4 sw=4: */
