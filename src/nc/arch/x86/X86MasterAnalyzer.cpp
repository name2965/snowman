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

#include "X86MasterAnalyzer.h"

#include <algorithm>
#include <climits>
#include <cstddef>
#include <functional>
#include <limits>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include <boost/optional.hpp>

#include <nc/common/Foreach.h>
#include <nc/common/StringToInt.h>
#include <nc/common/make_unique.h>

#include <nc/core/Context.h>
#include <nc/core/arch/Capstone.h>
#include <nc/core/arch/Disassembler.h>
#include <nc/core/arch/Instructions.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Platform.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Section.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/mangling/Demangler.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Program.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallSignature.h>
#include <nc/core/ir/calling/CallHook.h>
#include <nc/core/ir/calling/Convention.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/FunctionSignature.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/ImportedFunctionResolver.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/calling/SymbolPrototypeRegistry.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/dflow/Value.h>

#include "X86Architecture.h"
#include "X86Instruction.h"
#include "X86Registers.h"
#include "udis86.h"

namespace nc {
namespace arch {
namespace x86 {

namespace {

QString windowsDebuggerSymbolLeaf(QString name) {
    name = name.trimmed();

    if (name.size() >= 2 && name.startsWith(QLatin1Char('<')) &&
        name.endsWith(QLatin1Char('>')))
    {
        name = name.mid(1, name.size() - 2);
    }

    const int moduleSeparator = name.lastIndexOf(QLatin1Char('!'));
    if (moduleSeparator >= 0) {
        name = name.mid(moduleSeparator + 1);
    }

    bool jumpDisplayWrapper = false;
    if (name.startsWith(QLatin1String("JMP."), Qt::CaseInsensitive)) {
        name.remove(0, 4);
        jumpDisplayWrapper = true;
    }

    /* x64dbg prints import thunks as JMP.&name.  An ampersand outside that
     * known display wrapper may be part of a real debugger symbol. */
    if (jumpDisplayWrapper && name.startsWith(QLatin1Char('&'))) {
        name.remove(0, 1);
    }

    if (name.startsWith(QLatin1String("__imp_"))) {
        name.remove(0, 6);
    }

    return name.trimmed();
}

QString canonicalWindowsDebuggerSymbolName(QString name) {
    name = windowsDebuggerSymbolLeaf(std::move(name));

    /* Strip x86 stdcall decoration only as one complete `_name@N` form.
     * Removing a bare leading underscore or a bare @ suffix can merge two
     * distinct external symbols. */
    const int suffix = name.lastIndexOf(QLatin1Char('@'));
    if (name.startsWith(QLatin1Char('_')) && suffix > 1 &&
        suffix + 1 < name.size())
    {
        bool decimal = true;
        for (int index = suffix + 1; index < name.size(); ++index) {
            const unsigned short character = name.at(index).unicode();
            if (character < '0' || character > '9') {
                decimal = false;
                break;
            }
        }
        if (decimal) {
            name = name.mid(1, suffix - 1);
        }
    }

    return name.trimmed();
}

QString canonicalWindowsExternalModuleName(QString name) {
    /* Preserve the complete identity. Basename extraction or adding a
     * missing .dll suffix could promote an unrelated module to a trusted
     * provider entry. Providers must enumerate aliases deliberately. */
    return name.toLower();
}

QString operatingSystemName(core::image::Platform::OperatingSystem os) {
    switch (os) {
        case core::image::Platform::Windows:
            return QLatin1String("windows");
        case core::image::Platform::DOS:
            return QLatin1String("dos");
        case core::image::Platform::UnknownOS:
            return QLatin1String("unknown");
    }
    return QLatin1String("unknown");
}

const core::ir::calling::SymbolPrototypeRegistry &getPrototypeRegistry(
        core::Context &context) {
    if (context.symbolPrototypeRegistry()) {
        return *context.symbolPrototypeRegistry();
    }

    std::unique_ptr<core::ir::calling::SymbolPrototypeRegistry> registry(
        new core::ir::calling::SymbolPrototypeRegistry());
    const core::ir::calling::SymbolPrototypeTarget target(
        QLatin1String("x86"),
        operatingSystemName(context.image()->platform().operatingSystem()),
        context.image()->platform().architecture()->bitness());

    for (const auto &provider : context.symbolPrototypeProviders()) {
        if (provider) {
            registry->addProvider(*provider, target);
        }
    }
    context.setSymbolPrototypeRegistry(std::move(registry));
    return *context.symbolPrototypeRegistry();
}

const core::ir::calling::SymbolPrototypeRecord *getSymbolPrototype(
        const core::ir::calling::SymbolPrototypeRegistry &registry,
        const core::image::Symbol &symbol) {
    const core::image::ExternalNameOrigin origin =
        symbol.externalNameOrigin();
    if (origin == core::image::ExternalNameOrigin::UNKNOWN) {
        return nullptr;
    }

    QString moduleName = symbol.moduleName();
    QString symbolName = symbol.name();
    if (origin == core::image::ExternalNameOrigin::DEBUGGER) {
        QString decoratedName = symbolName.trimmed();
        if (decoratedName.size() >= 2 &&
            decoratedName.startsWith(QLatin1Char('<')) &&
            decoratedName.endsWith(QLatin1Char('>')))
        {
            decoratedName = decoratedName.mid(1, decoratedName.size() - 2);
        }
        const int separator = decoratedName.lastIndexOf(QLatin1Char('!'));
        if (separator >= 0) {
            const QString embeddedModule =
                decoratedName.left(separator);
            if (!moduleName.isEmpty() &&
                canonicalWindowsExternalModuleName(moduleName) !=
                    canonicalWindowsExternalModuleName(embeddedModule))
            {
                /* Never combine the trusted module from an import descriptor
                 * with a leaf name displayed for a different module. */
                return nullptr;
            }
            moduleName = embeddedModule;
            symbolName = decoratedName.mid(separator + 1);
        } else {
            symbolName = decoratedName;
        }
        symbolName = canonicalWindowsDebuggerSymbolName(symbolName);
    }

    /* OBJECT_FILE names are linker identities, not decorated display
     * strings. In particular, whitespace, _foo, __imp_foo and foo@N may all
     * name distinct exports and are therefore preserved byte-for-byte. */

    return registry.lookup(
        canonicalWindowsExternalModuleName(moduleName),
        symbolName);
}

const core::image::Symbol *getImportSymbolAtSlot(const core::image::Image &image, ByteAddr slot) {
    const auto relocation = image.getRelocation(slot);
    const SmallBitSize bitness =
        image.platform().architecture()->bitness();
    if (relocation && bitness > 0 && bitness % CHAR_BIT == 0 &&
        relocation->address() == slot && relocation->addend() == 0 &&
        relocation->size() == bitness / CHAR_BIT &&
        relocation->symbol()->type() == core::image::SymbolType::FUNCTION &&
        !relocation->symbol()->value())
    {
        return relocation->symbol();
    }
    return nullptr;
}

/* Resolve a decoded indirect call/jump whose static memory operand is an import slot. */
const core::image::Symbol *getIndirectImport(const core::image::Image &image,
                                             ByteAddr instructionAddress,
                                             X86Instruction::ControlTransferKind kind,
                                             ByteAddr *slotAddress = nullptr) {
    const auto section = image.getSectionContainingAddress(instructionAddress);
    if (!section || !section->isExecutable()) {
        return nullptr;
    }

    auto disassembler = image.platform().architecture()->createDisassembler();
    const auto instruction =
        disassembler->disassembleSingleInstruction(instructionAddress, &image);
    const auto x86Instruction =
        dynamic_cast<const X86Instruction *>(instruction.get());
    if (!x86Instruction) {
        return nullptr;
    }

    ByteAddr slot = 0;
    if (!x86Instruction->getStaticMemoryControlTransferAddress(kind, slot)) {
        return nullptr;
    }

    const auto symbol = getImportSymbolAtSlot(image, slot);
    if (symbol && slotAddress) {
        *slotAddress = slot;
    }
    return symbol;
}

const core::image::Symbol *getImportedFunctionSymbol(const core::image::Image &image,
                                                     const core::ir::calling::CalleeId &calleeId) {
    if (calleeId.entryAddress()) {
        /* A direct call can target a linker thunk which jumps through an IAT slot. */
        if (auto symbol = getIndirectImport(
                image, *calleeId.entryAddress(),
                X86Instruction::ControlTransferKind::JUMP))
        {
            return symbol;
        }

        /*
         * A debugger can also provide a symbol for an already resolved
         * external target. Never use this fallback inside the image: a local
         * function named like an API must not inherit its effects or noreturn
         * property. Local import thunks were resolved through their IAT
         * relocation above.
         */
        foreach (const auto section, image.sections()) {
            if (section->containsAddress(*calleeId.entryAddress())) {
                return nullptr;
            }
        }
        const auto symbol = image.getSymbol(*calleeId.entryAddress());
        if (symbol && symbol->type() == core::image::SymbolType::FUNCTION &&
            symbol->externalNameOrigin() ==
                core::image::ExternalNameOrigin::DEBUGGER)
        {
            return symbol;
        }
    } else if (calleeId.callAddress()) {
        /* An unresolved "call [IAT]" is identified by its instruction address. */
        return getIndirectImport(
            image, *calleeId.callAddress(),
            X86Instruction::ControlTransferKind::CALL);
    }

    return nullptr;
}

const core::image::Symbol *getImportedFunctionSymbol(const core::image::Image &image,
                                                     const core::ir::Call *call,
                                                     const core::ir::dflow::Dataflow &dataflow,
                                                     bool *usesMutableImportSlot = nullptr) {
    assert(call != nullptr);
    if (usesMutableImportSlot) {
        *usesMutableImportSlot = false;
    }

    /* Resolve the value actually reaching this call. This handles direct
     * [IAT] calls, register copies, and control-flow merges while rejecting a
     * visible full or partial overwrite of the relocation-backed slot. */
    if (const auto symbol = core::ir::calling::resolveImportedFunction(
            call, dataflow, image))
    {
        if (usesMutableImportSlot) {
            *usesMutableImportSlot = true;
        }
        return symbol;
    }

    if (const auto target = call->target()->asConstant()) {
        const ConstantValue targetValue = target->value().value();
        if (targetValue <= static_cast<ConstantValue>(
                (std::numeric_limits<ByteAddr>::max)()))
        {
            const ByteAddr targetAddress =
                static_cast<ByteAddr>(targetValue);
            foreach (const auto section, image.sections()) {
                if (!section->containsAddress(targetAddress)) {
                    continue;
                }

                /* A direct call to a local import thunk observes the slot at
                 * runtime. Reuse the same caller-CFG overwrite proof before
                 * attaching its contract or applying destructive noreturn
                 * semantics. */
                ByteAddr slot = 0;
                const auto symbol = getIndirectImport(
                    image, targetAddress,
                    X86Instruction::ControlTransferKind::JUMP, &slot);
                const SmallBitSize pointerSize =
                    image.platform().architecture()->bitness();
                if (symbol &&
                    core::ir::calling::isImportSlotUnmodifiedBefore(
                        call, dataflow, pointerSize, slot))
                {
                    if (usesMutableImportSlot) {
                        *usesMutableImportSlot = true;
                    }
                    return symbol;
                }
                return nullptr;
            }

            /* A debugger-resolved direct target outside the image is already
             * a concrete function value; no mutable image slot is involved. */
            const auto symbol = image.getSymbol(targetAddress);
            if (symbol &&
                symbol->type() == core::image::SymbolType::FUNCTION &&
                symbol->externalNameOrigin() ==
                    core::image::ExternalNameOrigin::DEBUGGER)
            {
                return symbol;
            }
        }
    }

    return nullptr;
}

/**
 * A relocation proves the initial contents of an import slot, not that the
 * program leaves that slot immutable. Local reaching definitions cover the
 * path to one call; this additional image-wide guard prevents contracts (and
 * especially destructive noreturn CFG edits) from surviving when another
 * analyzed function can visibly patch any equivalent slot.
 */
bool isImportSymbolStableAcrossProgram(
        const core::Context &context, const core::image::Symbol *symbol) {
    if (!symbol || !context.image() || !context.dataflows()) {
        return false;
    }

    const auto architecture = context.image()->platform().architecture();
    if (!architecture || architecture->bitness() <= 0 ||
        architecture->bitness() % CHAR_BIT != 0)
    {
        return false;
    }

    const SmallBitSize pointerSize = architecture->bitness();
    const ByteSize pointerBytes = pointerSize / CHAR_BIT;
    bool foundExactSlot = false;
    foreach (const auto relocation, context.image()->relocations()) {
        if (!relocation || relocation->symbol() != symbol ||
            relocation->size() != pointerBytes || relocation->addend() != 0)
        {
            continue;
        }
        foundExactSlot = true;
        for (const auto &functionAndDataflow : *context.dataflows()) {
            if (!functionAndDataflow.second ||
                core::ir::calling::mayFunctionOverwriteImportSlot(
                    functionAndDataflow.first, *functionAndDataflow.second,
                    pointerSize, relocation->address()))
            {
                return false;
            }
        }
    }
    return foundExactSlot;
}

void addImportThunkAlias(core::image::Image &image, ByteAddr address) {
    const auto section = image.getSectionContainingAddress(address);
    if (!section || !section->isExecutable()) {
        return;
    }

    const auto existingSymbol = image.getSymbol(address);
    if (existingSymbol && !existingSymbol->name().isEmpty()) {
        return;
    }

    const auto importSymbol = getIndirectImport(
        image, address, X86Instruction::ControlTransferKind::JUMP);
    if (!importSymbol || importSymbol->name().isEmpty()) {
        return;
    }

    image.addSymbol(std::make_unique<core::image::Symbol>(
        core::image::SymbolType::FUNCTION, importSymbol->name(), address,
        nullptr, importSymbol->moduleName(),
        importSymbol->externalNameOrigin()));
}

/*
 * Give linker thunks a function name only when control-flow recovery has
 * established their entry boundary.  This replaces executable-section byte
 * scanning, which could interpret embedded data or the middle of another
 * instruction as a thunk.
 */
void addImportThunkAliases(core::Context &context) {
    auto &image = *context.image();

    foreach (ByteAddr address, context.program()->calledAddresses()) {
        addImportThunkAlias(image, address);
    }

    foreach (const auto function, context.functions()->list()) {
        if (function->entry() && function->entry()->address()) {
            addImportThunkAlias(image, *function->entry()->address());
        }
    }
}

boost::optional<ByteSize> getPrototypeStackArgumentsSize(
        const core::ir::calling::SymbolPrototypeRecord &record,
        const core::ir::calling::Convention &convention) {
    if (!record.prototype() || convention.argumentAlignment() <= 0 ||
        convention.argumentAlignment() % CHAR_BIT != 0)
    {
        return boost::none;
    }

    /* Schema-v1 prototypes contain only integer/pointer scalars of at most
     * one ABI slot. The first convention group is the scalar register group;
     * every remaining parameter therefore occupies exactly one aligned stack
     * slot. Derive this duplicated fact instead of trusting a catalog byte
     * count blindly. Aggregates, floating point and varargs must use a future
     * schema which can describe their actual ABI classification. */
    const auto &groups = convention.argumentGroups();
    const std::size_t registerParameterCount =
        groups.empty() ? 0 : groups.front().size();
    const std::size_t parameterCount =
        record.prototype()->parameters().size();
    const std::size_t stackParameterCount =
        parameterCount > registerParameterCount ?
            parameterCount - registerParameterCount : 0;
    const ByteSize slotSize = convention.argumentAlignment() / CHAR_BIT;
    if (stackParameterCount > static_cast<std::size_t>(
            (std::numeric_limits<ByteSize>::max)() / slotSize))
    {
        return boost::none;
    }
    return static_cast<ByteSize>(stackParameterCount) * slotSize;
}

bool hasConsistentPrototypeLayout(
        const core::ir::calling::SymbolPrototypeRecord &record,
        const core::ir::calling::Convention &convention,
        SmallBitSize targetBitness) {
    if (!record.prototype() ||
        !core::ir::calling::isFunctionPrototypeTargetCompatible(
            *record.prototype(), targetBitness))
    {
        return false;
    }
    if (record.prototype() && record.prototype()->variadic()) {
        /* A variadic call has a call-site-specific trailing extent.  On x86
         * it therefore cannot use an ABI in which the callee performs a
         * fixed stack adjustment, even when the catalog correctly omits a
         * total stack_arguments_size.  Keep this check at the architecture
         * boundary: convention identifiers are data, not schema syntax. */
        if (convention.calleeCleanup() || record.stackArgumentsSize()) {
            return false;
        }
    }
    const auto derivedStackArgumentsSize =
        getPrototypeStackArgumentsSize(record, convention);
    return derivedStackArgumentsSize &&
        (!record.stackArgumentsSize() ||
         *record.stackArgumentsSize() == *derivedStackArgumentsSize);
}

bool getPrototypeCallingConvention(
        const core::Context &context,
        const core::ir::calling::SymbolPrototypeRecord &record,
        const core::ir::calling::Convention *&convention,
        boost::optional<ByteSize> &stackArgumentsSize) {
    convention =
        context.image()->platform().architecture()->getCallingConvention(
            record.conventionName());
    if (!convention) {
        return false;
    }

    if (!hasConsistentPrototypeLayout(
            record, *convention,
            context.image()->platform().architecture()->bitness()))
    {
        return false;
    }
    const auto derivedStackArgumentsSize =
        getPrototypeStackArgumentsSize(record, *convention);
    assert(derivedStackArgumentsSize);

    /* An external unknown is authoritative too: variadic calls have no
     * fixed total extent and must mask a persistent decorated-name size. */
    stackArgumentsSize = record.prototype()->variadic() ?
        boost::optional<ByteSize>() : derivedStackArgumentsSize;
    return true;
}

bool setExplicitThiscallConvention(core::Context &context,
                                   const core::ir::calling::CalleeId &calleeId,
                                   const QString &symbolName) {
    const QString demangledName = context.image()->demangler()->demangle(symbolName);

    /*
     * Do not guess from ECX usage: ordinary C functions commonly use ECX as a
     * temporary.  Microsoft's decorated names, on the other hand, carry the
     * calling convention and the demangler emits it as a separate keyword.
     */
    if (!demangledName.contains(QLatin1String(" __thiscall "))) {
        return false;
    }

    context.conventions()->setConvention(
        calleeId,
        context.image()->platform().architecture()->getCallingConvention(
            QLatin1String("thiscall32")));
    return true;
}

/**
 * Parses the Microsoft x86 stdcall decoration `_name@N`.
 *
 * A trailing decimal number alone is not a calling-convention marker.  In
 * particular, this intentionally rejects fastcall (`@name@N`) and import
 * pointer (`__imp__name@N`) spellings.
 */
boost::optional<ByteSize> getStdcallStackArgumentsSize(
        const QString &symbolName) {
    if (symbolName.size() < 4 ||
        symbolName.at(0).unicode() != '_' ||
        symbolName.startsWith(QLatin1String("__imp_")))
    {
        return boost::none;
    }

    const int separator = symbolName.indexOf(QLatin1Char('@'), 1);
    if (separator <= 1 ||
        symbolName.indexOf(QLatin1Char('@'), separator + 1) >= 0 ||
        separator + 1 == symbolName.size())
    {
        return boost::none;
    }

    for (int index = separator + 1; index < symbolName.size(); ++index) {
        const unsigned short character = symbolName.at(index).unicode();
        if (character < '0' || character > '9') {
            return boost::none;
        }
    }

    const auto argumentsSize =
        stringToInt<ByteSize>(symbolName.mid(separator + 1));
    /* A genuine x86 stdcall epilogue encodes its byte adjustment in the
     * unsigned 16-bit immediate of RET.  Reject decorations which cannot be
     * represented by that ABI instead of later truncating them to ESP width
     * or manufacturing a contradictory cleanup contract. */
    const ByteSize maximumStdcallCleanup = 0xffff;
    if (!argumentsSize || *argumentsSize < 0 ||
        *argumentsSize > maximumStdcallCleanup ||
        *argumentsSize % 4 != 0)
    {
        return boost::none;
    }
    return argumentsSize;
}

bool getDecoratedImportCallingConvention(
        const core::Context &context,
        const core::image::Symbol &symbol,
        const core::ir::calling::Convention *&convention,
        boost::optional<ByteSize> &stackArgumentsSize) {
    QString symbolName = symbol.name();
    if (symbol.externalNameOrigin() ==
            core::image::ExternalNameOrigin::DEBUGGER)
    {
        /* Keep `_name@N` intact for ABI recovery. Prototype lookup uses a
         * separately canonicalized leaf, but decoration is executable ABI
         * evidence and must not be erased before it is interpreted. */
        symbolName = windowsDebuggerSymbolLeaf(symbolName);
    }

    const auto architecture =
        context.image()->platform().architecture();
    if (architecture->bitness() != 32) {
        return false;
    }

    const QString demangledName =
        context.image()->demangler()->demangle(symbolName);
    if (demangledName.contains(QLatin1String(" __thiscall "))) {
        convention = architecture->getCallingConvention(
            QLatin1String("thiscall32"));
        if (!convention) {
            return false;
        }
        stackArgumentsSize = boost::none;
        return true;
    }

    const auto argumentsSize =
        getStdcallStackArgumentsSize(symbolName);
    convention = architecture->getCallingConvention(
        QLatin1String("stdcall32"));
    if (!argumentsSize || !convention) {
        return false;
    }
    stackArgumentsSize = argumentsSize;
    return true;
}

boost::optional<core::ir::MemoryLocation> getScalarArgumentLocation(
        const core::ir::calling::Convention &convention,
        std::size_t index, SmallBitSize valueSize) {
    if (valueSize <= 0) {
        return boost::none;
    }

    /*
     * FunctionPrototype currently describes integer and pointer scalars. By
     * Convention contract, their locations are the
     * first argument group.  This also preserves Microsoft x64 positional
     * slots: only parameters after all four scalar locations move to stack.
     */
    const auto &groups = convention.argumentGroups();
    const std::vector<core::ir::MemoryLocation> *scalarArguments =
        groups.empty() ? nullptr : &groups.front();
    const std::size_t registerArgumentCount =
        scalarArguments ? scalarArguments->size() : 0;
    if (index < registerArgumentCount) {
        const auto &location = (*scalarArguments)[index];
        if (!location || valueSize > location.size()) {
            return boost::none;
        }
        return location.resized(valueSize);
    }

    const BitSize firstArgumentOffset = convention.firstArgumentOffset();
    const BitSize argumentAlignment = convention.argumentAlignment();
    if (firstArgumentOffset < 0 || argumentAlignment <= 0 ||
        valueSize > argumentAlignment ||
        firstArgumentOffset % CHAR_BIT != 0 ||
        argumentAlignment % CHAR_BIT != 0)
    {
        return boost::none;
    }

    const std::size_t stackIndex = index - registerArgumentCount;
    const BitSize maxBitOffset = (std::numeric_limits<BitSize>::max)();
    if (static_cast<ConstantValue>(stackIndex) >
        static_cast<ConstantValue>(
            (maxBitOffset - firstArgumentOffset) / argumentAlignment))
    {
        return boost::none;
    }

    const BitSize bitOffset = firstArgumentOffset +
        static_cast<BitSize>(stackIndex) * argumentAlignment;
    return core::ir::MemoryLocation(
        core::ir::MemoryDomain::STACK, bitOffset, valueSize);
}

std::shared_ptr<core::ir::Term> makeScalarArgument(
        const core::ir::calling::Convention &convention,
        std::size_t index, SmallBitSize valueSize) {
    const auto location = getScalarArgumentLocation(
        convention, index, valueSize);
    if (!location) {
        return nullptr;
    }
    if (location->domain() != core::ir::MemoryDomain::STACK) {
        return std::make_shared<core::ir::MemoryLocationAccess>(*location);
    }

    const auto &stackPointer = convention.stackPointer();
    if (!stackPointer || location->addr() % CHAR_BIT != 0) {
        return nullptr;
    }
    const ByteSize byteOffset = location->addr() / CHAR_BIT;
    const SmallBitSize pointerSize = stackPointer.size<SmallBitSize>();

    return std::make_shared<core::ir::Dereference>(
        std::make_unique<core::ir::BinaryOperator>(
            core::ir::BinaryOperator::ADD,
            std::make_unique<core::ir::MemoryLocationAccess>(stackPointer),
            std::make_unique<core::ir::Constant>(
                SizedValue(pointerSize, byteOffset)),
            pointerSize),
        core::ir::MemoryDomain::MEMORY,
        location->size<SmallBitSize>());
}

std::shared_ptr<core::ir::Term> makeScalarReturnValue(
        const core::ir::calling::Convention &convention,
        SmallBitSize valueSize) {
    if (valueSize <= 0 || convention.returnValueLocations().empty()) {
        return nullptr;
    }

    /* Scalar return locations precede floating-point locations here. */
    const auto &location = convention.returnValueLocations().front();
    if (!location || valueSize > location.size()) {
        return nullptr;
    }
    return std::make_shared<core::ir::MemoryLocationAccess>(
        location.resized(valueSize));
}

std::shared_ptr<core::ir::calling::FunctionSignature> makeFunctionSignature(
        const core::ir::calling::SymbolPrototypeRecord &record,
        const core::ir::calling::Convention &convention) {
    const auto &prototype = record.prototype();
    if (!prototype) {
        return nullptr;
    }

    auto signature = std::make_shared<core::ir::calling::FunctionSignature>();
    signature->setPrototype(prototype);
    signature->setVariadic(prototype->variadic());

    for (std::size_t index = 0;
         index < prototype->parameters().size(); ++index)
    {
        const auto &type = prototype->parameters()[index].type();
        if (type.kind() == core::ir::calling::TypeDescription::VOID) {
            return nullptr;
        }
        auto argument = makeScalarArgument(
            convention, index, type.size());
        if (!argument) {
            return nullptr;
        }
        signature->arguments().push_back(std::move(argument));
    }

    if (prototype->returnType().kind() !=
        core::ir::calling::TypeDescription::VOID)
    {
        auto returnValue = makeScalarReturnValue(
            convention, prototype->returnType().size());
        if (!returnValue) {
            return nullptr;
        }
        signature->setReturnValue(std::move(returnValue));
    }

    return signature;
}

std::shared_ptr<core::ir::calling::FunctionSignature> makeCallbackSignature(
        const core::ir::calling::FunctionPrototype &callback,
        const QString &preferredName,
        const core::ir::calling::Convention &convention) {
    auto signature = std::make_shared<core::ir::calling::FunctionSignature>();

    signature->setPrototype(
        std::make_shared<core::ir::calling::FunctionPrototype>(
            callback.returnType(), callback.parameters(),
            callback.callingConvention(), preferredName,
            callback.memoryEffectsAreComplete(),
            callback.abiConventionName(), callback.variadic()));
    signature->setVariadic(callback.variadic());

    for (std::size_t index = 0;
         index < callback.parameters().size(); ++index)
    {
        const auto &type = callback.parameters()[index].type();
        if (type.kind() == core::ir::calling::TypeDescription::VOID) {
            return nullptr;
        }
        auto argument = makeScalarArgument(
            convention, index, type.size());
        if (!argument) {
            return nullptr;
        }
        signature->arguments().push_back(std::move(argument));
    }

    if (callback.returnType().kind() !=
        core::ir::calling::TypeDescription::VOID)
    {
        auto returnValue = makeScalarReturnValue(
            convention, callback.returnType().size());
        if (!returnValue) {
            return nullptr;
        }
        signature->setReturnValue(std::move(returnValue));
    }
    return signature;
}

boost::optional<ByteAddr> toByteAddress(ConstantValue value) {
    if (value > static_cast<ConstantValue>(
            (std::numeric_limits<ByteAddr>::max)()))
    {
        return boost::none;
    }
    return static_cast<ByteAddr>(value);
}

boost::optional<ByteAddr> getConcreteAddress(
        const core::ir::Term *term,
        const core::ir::dflow::Dataflow &dataflow) {
    if (!term) {
        return boost::none;
    }
    const auto value = dataflow.findValue(term);
    if (!value || !value->abstractValue().isConcrete()) {
        return boost::none;
    }
    return toByteAddress(value->abstractValue().asConcrete().value());
}

boost::optional<ByteAddr> getConcreteAddress(
        const core::ir::Statement *snapshot,
        const core::ir::MemoryLocation &location,
        const core::ir::dflow::Dataflow &dataflow) {
    assert(snapshot != nullptr);
    assert(location);

    const auto definitions =
        dataflow.getDefinitions(snapshot).projected(location);
    if (definitions.chunks().size() != 1 ||
        definitions.chunks().front().location() != location ||
        definitions.chunks().front().hasUnknownDefinition() ||
        definitions.chunks().front().hasIncomingDefinition() ||
        definitions.chunks().front().definitions().empty())
    {
        return boost::none;
    }

    boost::optional<ConstantValue> result;
    foreach (const auto definition,
             definitions.chunks().front().definitions()) {
        const auto value = dataflow.findValue(definition);
        if (!value || !value->abstractValue().isConcrete()) {
            return boost::none;
        }

        const ConstantValue concrete =
            value->abstractValue().asConcrete().value();
        if (result && *result != concrete) {
            return boost::none;
        }
        result = concrete;
    }

    if (!result) {
        return boost::none;
    }
    return toByteAddress(*result);
}

boost::optional<ByteAddr> getConcreteCallArgument(
        const core::ir::Call *call,
        const core::ir::dflow::Dataflow &dataflow,
        const core::ir::calling::Hooks &hooks,
        const core::ir::calling::CallSignature *signature,
        std::size_t index,
        const core::ir::calling::Convention &convention,
        SmallBitSize valueSize) {
    if (!dataflow.converged()) {
        /* Callback discovery creates a persistent function signature.  Do
         * not derive one from a bounded provisional constant. */
        return boost::none;
    }

    const auto callHook = hooks.getCallHook(call);
    if (!callHook) {
        return boost::none;
    }

    if (signature && index < signature->arguments().size()) {
        const auto argument = signature->arguments()[index].get();
        if (const auto hookTerm = callHook->getArgumentTerm(argument)) {
            if (const auto address = getConcreteAddress(hookTerm, dataflow)) {
                return address;
            }
        }
    }

    const auto snapshot = callHook->snapshotStatement();
    const auto argumentLocation = getScalarArgumentLocation(
        convention, index, valueSize);
    if (!snapshot || !argumentLocation) {
        return boost::none;
    }

    if (argumentLocation->domain() != core::ir::MemoryDomain::STACK) {
        return getConcreteAddress(
            snapshot, *argumentLocation, dataflow);
    }

    if (!callHook->stackPointer() ||
        argumentLocation->addr() % CHAR_BIT != 0)
    {
        return boost::none;
    }
    const auto stackPointerValue =
        dataflow.findValue(callHook->stackPointer());
    if (!stackPointerValue || !stackPointerValue->isStackOffset()) {
        return boost::none;
    }

    const ByteSize offset = argumentLocation->addr() / CHAR_BIT;

    const SignedConstantValue stackOffset = stackPointerValue->stackOffset();
    if (stackOffset >
        (std::numeric_limits<SignedConstantValue>::max)() - offset)
    {
        return boost::none;
    }
    const SignedConstantValue argumentByteAddress = stackOffset + offset;
    const BitAddr maximumStart =
        (std::numeric_limits<BitAddr>::max)() -
        argumentLocation->size();
    if (argumentByteAddress <
            (std::numeric_limits<BitAddr>::min)() / CHAR_BIT ||
        argumentByteAddress > maximumStart / CHAR_BIT)
    {
        return boost::none;
    }
    const BitAddr argumentAddress = argumentByteAddress * CHAR_BIT;
    const core::ir::MemoryLocation concreteLocation(
        core::ir::MemoryDomain::STACK, argumentAddress,
        argumentLocation->size());
    return getConcreteAddress(snapshot, concreteLocation, dataflow);
}

core::ir::Function *getFunctionAtAddress(core::Context &context, ByteAddr address) {
    foreach (auto function, context.functions()->list()) {
        if (function->entry() && function->entry()->address() &&
            *function->entry()->address() == address)
        {
            return function;
        }
    }
    return nullptr;
}

bool isTrustedLocalFunctionEntry(const core::Context &context,
                                 ByteAddr address) {
    const auto section =
        context.image()->getSectionContainingAddress(address);
    if (!section || !section->isExecutable()) {
        return false;
    }

    /*
     * A function-pointer value proves intent, but not that an arbitrary byte
     * is a valid instruction boundary. Require the exact start of an
     * instruction already selected by the disassembly and represented in the
     * Program. This rejects interior-byte constants and avoids manufacturing
     * empty functions outside the requested disassembly range.
     */
    const auto &instruction = context.instructions()->get(address);
    if (!instruction || instruction->size() <= 0 ||
        address > (std::numeric_limits<ByteAddr>::max)() -
            instruction->size())
    {
        return false;
    }
    const ByteAddr lastInstructionByte =
        address + instruction->size() - 1;
    if (!section->containsAddress(lastInstructionByte)) {
        return false;
    }

    return context.program()->getBasicBlockStartingAt(address) != nullptr ||
        context.program()->getBasicBlockCovering(address) != nullptr;
}

QString getCallbackPreferredName(
        const core::Context &context, ByteAddr address,
        const core::ir::calling::FunctionPrototype &callback,
        const std::map<QString, std::size_t> &hintUseCounts) {
    if (callback.preferredName().isEmpty()) {
        return QString();
    }

    const QString hint = callback.preferredName();
    const QString hintKey = hint.toLower();
    const auto useCount = hintUseCounts.find(hintKey);
    const auto addressSymbol = context.image()->getSymbol(address);
    if (useCount == hintUseCounts.end() || useCount->second != 1 ||
        (addressSymbol && !addressSymbol->name().trimmed().isEmpty())) {
        return QString();
    }

    foreach (const auto symbol, context.image()->symbols()) {
        const QString comparableName =
            symbol->externalNameOrigin() ==
                    core::image::ExternalNameOrigin::DEBUGGER ?
                canonicalWindowsDebuggerSymbolName(symbol->name()) :
                symbol->name().trimmed();
        if (comparableName.compare(
                hint, Qt::CaseInsensitive) == 0)
        {
            return QString();
        }
    }

    foreach (const auto function, context.functions()->list()) {
        if (function->entry() && function->entry()->address() &&
            *function->entry()->address() == address)
        {
            continue;
        }
        const auto signature = context.signatures()->getSignature(function);
        if (signature && signature->prototype() &&
            signature->prototype()->preferredName().compare(
                hint, Qt::CaseInsensitive) == 0)
        {
            return QString();
        }
    }

    return hint;
}

void setFunctionSignature(core::Context &context,
                          const core::ir::calling::CalleeId &calleeId,
                          const std::shared_ptr<core::ir::calling::FunctionSignature> &signature,
                          const core::ir::Function *function = nullptr) {
    if (calleeId.entryAddress()) {
        context.signatures()->setSignature(
            *calleeId.entryAddress(), signature,
            core::ir::calling::SignatureSource::EXTERNAL);
    }
    if (function) {
        context.signatures()->setSignature(
            function, signature,
            core::ir::calling::SignatureSource::EXTERNAL);
    }
}

void setCallSignature(core::Context &context,
                      const std::shared_ptr<core::ir::calling::FunctionSignature> &functionSignature,
                      const core::ir::Call *call) {
    auto callSignature = std::make_shared<core::ir::calling::CallSignature>();

    callSignature->arguments() = functionSignature->arguments();
    const auto &prototype = functionSignature->prototype();
    const auto previousSignature = context.signatures()->getSignature(
        call, core::ir::calling::SignatureSource::INFERRED);
    if (prototype && prototype->variadic() && previousSignature &&
        (previousSignature->argumentEvidence() ==
             core::ir::calling::CallSignature::ArgumentEvidence::
                 VARIADIC_TAIL ||
         previousSignature->arguments().size() >
             callSignature->arguments().size()))
    {
        auto firstVariadic = previousSignature->arguments().begin();
        if (previousSignature->argumentEvidence() !=
                core::ir::calling::CallSignature::ArgumentEvidence::
                    VARIADIC_TAIL)
        {
            firstVariadic += callSignature->arguments().size();
        }
        callSignature->arguments().insert(
            callSignature->arguments().end(), firstVariadic,
            previousSignature->arguments().end());
    }
    callSignature->setReturnValue(functionSignature->returnValue());
    callSignature->setPrototype(prototype);
    context.signatures()->setSignature(
        call, callSignature,
        core::ir::calling::SignatureSource::EXTERNAL);
}

bool haveCompatibleTypeLayout(
        const core::ir::calling::TypeDescription &left,
        const core::ir::calling::TypeDescription &right) {
    return left.kind() == right.kind() && left.size() == right.size() &&
           left.isUnsigned() == right.isUnsigned();
}

QString mergePresentationName(const QString &left, const QString &right) {
    /* Keep a presentation hint only when every observation agrees exactly.
     * Empty is deliberately absorbing: it can represent either missing
     * evidence or a conflict discarded by an earlier merge. This makes the
     * reduction associative and independent of unordered traversal order. */
    return left == right ? left : QString();
}

core::ir::calling::TypeDescription mergeTypePresentation(
        const core::ir::calling::TypeDescription &left,
        const core::ir::calling::TypeDescription &right) {
    assert(haveCompatibleTypeLayout(left, right));
    return core::ir::calling::TypeDescription(
        left.kind(), left.size(), left.isUnsigned(),
        mergePresentationName(left.displayName(), right.displayName()));
}

core::ir::calling::ParameterDescription::PointeeAccess mergePointeeAccess(
        core::ir::calling::ParameterDescription::PointeeAccess left,
        core::ir::calling::ParameterDescription::PointeeAccess right) {
    using Access = core::ir::calling::ParameterDescription::PointeeAccess;
    const bool mayRead = left == Access::READ ||
        left == Access::READ_WRITE || right == Access::READ ||
        right == Access::READ_WRITE;
    const bool mayWrite = left == Access::WRITE ||
        left == Access::READ_WRITE || right == Access::WRITE ||
        right == Access::READ_WRITE;
    if (mayRead && mayWrite) {
        return Access::READ_WRITE;
    }
    if (mayRead) {
        return Access::READ;
    }
    if (mayWrite) {
        return Access::WRITE;
    }
    return Access::NONE;
}

typedef std::pair<const core::ir::calling::FunctionPrototype *,
                  const core::ir::calling::FunctionPrototype *>
    PrototypeMergePair;

struct PrototypeMergePairLess {
    bool operator()(const PrototypeMergePair &left,
                    const PrototypeMergePair &right) const {
        std::less<const core::ir::calling::FunctionPrototype *> less;
        if (less(left.first, right.first)) {
            return true;
        }
        if (less(right.first, left.first)) {
            return false;
        }
        return less(left.second, right.second);
    }
};

struct PrototypeMergeTraversal {
    typedef std::shared_ptr<const core::ir::calling::FunctionPrototype>
        Result;

    std::map<PrototypeMergePair, Result, PrototypeMergePairLess> results;
    std::set<PrototypeMergePair, PrototypeMergePairLess> active;
    std::size_t parameterVisits = 0;
};

const unsigned int MAX_CALLBACK_MERGE_DEPTH = 16;
const std::size_t MAX_CALLBACK_MERGE_PAIRS = 4096;
const std::size_t MAX_CALLBACK_MERGE_PARAMETERS = 65536;

std::shared_ptr<const core::ir::calling::FunctionPrototype>
mergeCompatiblePrototypesImpl(
        const core::ir::calling::FunctionPrototype &left,
        const core::ir::calling::FunctionPrototype &right,
        unsigned int callbackDepth,
        PrototypeMergeTraversal &traversal) {
    typedef std::shared_ptr<const core::ir::calling::FunctionPrototype>
        Result;
    const PrototypeMergePair pair(&left, &right);
    const auto known = traversal.results.find(pair);
    if (known != traversal.results.end()) {
        return known->second;
    }

    if (!haveCompatibleTypeLayout(left.returnType(), right.returnType()) ||
        left.callingConvention() != right.callingConvention() ||
        left.abiConventionName() != right.abiConventionName() ||
        left.variadic() != right.variadic() ||
        left.parameters().size() != right.parameters().size() ||
        callbackDepth > MAX_CALLBACK_MERGE_DEPTH ||
        left.parameters().size() > 1024 ||
        traversal.results.size() + traversal.active.size() >=
            MAX_CALLBACK_MERGE_PAIRS ||
        left.parameters().size() >
            MAX_CALLBACK_MERGE_PARAMETERS - traversal.parameterVisits)
    {
        traversal.results.emplace(pair, Result());
        return nullptr;
    }

    if (!traversal.active.insert(pair).second) {
        /* Cyclic programmatic metadata is not a representable immutable
         * source prototype and must not recurse indefinitely. */
        traversal.results.emplace(pair, Result());
        return nullptr;
    }
    traversal.parameterVisits += left.parameters().size();

    const auto finish = [&](const Result &result) -> Result {
        traversal.active.erase(pair);
        traversal.results.emplace(pair, result);
        return result;
    };

    std::vector<core::ir::calling::ParameterDescription> parameters;
    parameters.reserve(left.parameters().size());
    bool parameterEffectsAgree = true;
    bool hasNestedCallback = false;
    for (std::size_t index = 0; index < left.parameters().size(); ++index) {
        const auto &leftParameter = left.parameters()[index];
        const auto &rightParameter = right.parameters()[index];
        if (!haveCompatibleTypeLayout(
                leftParameter.type(), rightParameter.type())) {
            return finish(Result());
        }

        const auto &leftCallback = leftParameter.callbackPrototype();
        const auto &rightCallback = rightParameter.callbackPrototype();
        if (static_cast<bool>(leftCallback) !=
            static_cast<bool>(rightCallback))
        {
            return finish(Result());
        }
        std::shared_ptr<const core::ir::calling::FunctionPrototype>
            mergedCallback;
        if (leftCallback) {
            hasNestedCallback = true;
            if (leftCallback.get() == rightCallback.get()) {
                mergedCallback = leftCallback;
            } else {
                mergedCallback = mergeCompatiblePrototypesImpl(
                    *leftCallback, *rightCallback, callbackDepth + 1,
                    traversal);
            }
            if (!mergedCallback) {
                return finish(Result());
            }
        }

        parameterEffectsAgree = parameterEffectsAgree &&
            leftParameter.pointeeAccess() ==
                rightParameter.pointeeAccess();
        parameters.push_back(core::ir::calling::ParameterDescription(
            mergePresentationName(
                leftParameter.name(), rightParameter.name()),
            mergeTypePresentation(
                leftParameter.type(), rightParameter.type()),
            mergePointeeAccess(
                leftParameter.pointeeAccess(),
                rightParameter.pointeeAccess()),
            std::move(mergedCallback)));
    }

    const bool effectsComplete = !hasNestedCallback &&
        parameterEffectsAgree &&
        left.memoryEffectsAreComplete() &&
        right.memoryEffectsAreComplete();
    return finish(std::make_shared<const
        core::ir::calling::FunctionPrototype>(
        mergeTypePresentation(left.returnType(), right.returnType()),
        std::move(parameters), left.callingConvention(),
        mergePresentationName(
            left.preferredName(), right.preferredName()),
        effectsComplete, left.abiConventionName(), left.variadic()));
}

std::shared_ptr<const core::ir::calling::FunctionPrototype>
mergeCompatiblePrototypes(
        const core::ir::calling::FunctionPrototype &left,
        const core::ir::calling::FunctionPrototype &right) {
    PrototypeMergeTraversal traversal;
    return mergeCompatiblePrototypesImpl(
        left, right, 0, traversal);
}

struct RecoveredCallback {
    std::shared_ptr<const core::ir::calling::FunctionPrototype> prototype;
    bool conflictingPrototype;

    RecoveredCallback(): conflictingPrototype(false) {}

    void merge(const std::shared_ptr<const core::ir::calling::FunctionPrototype>
                   &candidate) {
        assert(candidate != nullptr);
        if (conflictingPrototype) {
            return;
        }
        if (!prototype) {
            prototype = candidate;
        } else if (prototype.get() == candidate.get()) {
            /* Repeated observations of one immutable DAG add no information.
             * Preserve its sharing instead of cloning the full graph. */
            return;
        } else {
            const auto merged = mergeCompatiblePrototypes(
                *prototype, *candidate);
            if (merged) {
                prototype = merged;
            } else {
                conflictingPrototype = true;
            }
        }
    }
};

class CallbackCallEvidence {
    std::size_t proofs_;
    boost::optional<ByteAddr> address_;
    RecoveredCallback callback_;
    bool conflictingAddress_;

public:
    CallbackCallEvidence(): proofs_(0), conflictingAddress_(false) {}

    void prove(
            ByteAddr address,
            const std::shared_ptr<const
                core::ir::calling::FunctionPrototype> &prototype) {
        ++proofs_;
        if (address_ && *address_ != address) {
            conflictingAddress_ = true;
        } else {
            address_ = address;
        }
        callback_.merge(prototype);
    }

    bool isProved(std::size_t observations) const {
        return observations != 0 && proofs_ == observations && address_ &&
            !conflictingAddress_ && !callback_.conflictingPrototype &&
            callback_.prototype;
    }

    void publish(std::map<ByteAddr, RecoveredCallback> &callbacks) const {
        assert(address_ && callback_.prototype);
        callbacks[*address_].merge(callback_.prototype);
    }
};

const core::ir::calling::Convention *getCallbackConvention(
        const core::Context &context,
        const core::ir::calling::FunctionPrototype &callback) {
    const auto architecture = context.image()->platform().architecture();
    const auto convention = architecture->getCallingConvention(
        callback.abiConventionName());
    return convention && (!callback.variadic() || !convention->calleeCleanup()) ?
        convention : nullptr;
}

boost::optional<ByteSize> getCallbackStackArgumentsSize(
        const core::ir::calling::FunctionPrototype &callback,
        const core::ir::calling::Convention &convention) {
    const BitSize alignment = convention.argumentAlignment();
    if (alignment <= 0 || alignment % CHAR_BIT != 0) {
        return boost::none;
    }

    const auto &groups = convention.argumentGroups();
    const std::size_t registerParameterCount =
        groups.empty() ? 0 : groups.front().size();
    const std::size_t stackParameterCount =
        callback.parameters().size() > registerParameterCount ?
            callback.parameters().size() - registerParameterCount : 0;
    const ByteSize slotSize = alignment / CHAR_BIT;
    if (stackParameterCount > static_cast<std::size_t>(
            (std::numeric_limits<ByteSize>::max)() / slotSize))
    {
        return boost::none;
    }
    return static_cast<ByteSize>(stackParameterCount) * slotSize;
}

core::ir::Call *findProgramCallAt(
        core::ir::Program &program, ByteAddr instructionAddress) {
    core::ir::Call *result = nullptr;
    foreach (auto basicBlock, program.basicBlocks()) {
        foreach (auto statement, basicBlock->statements()) {
            auto call = statement->as<core::ir::Call>();
            if (!call || !call->instruction() ||
                call->instruction()->addr() != instructionAddress)
            {
                continue;
            }
            /* More than one lowered Call at one machine instruction would
             * make the Function-to-Program correspondence ambiguous. */
            if (result) {
                return nullptr;
            }
            result = call;
        }
    }
    return result;
}

class NoReturnCallEvidence {
    std::size_t observations_;
    std::size_t proofs_;
    const core::image::Symbol *symbol_;
    bool conflicting_;

public:
    NoReturnCallEvidence():
        observations_(0), proofs_(0), symbol_(nullptr), conflicting_(false)
    {}

    void observe() { ++observations_; }

    void prove(const core::image::Symbol *symbol) {
        assert(symbol != nullptr);
        ++proofs_;
        if (symbol_ && symbol_ != symbol) {
            conflicting_ = true;
        } else {
            symbol_ = symbol;
        }
    }

    bool isProved() const {
        return observations_ != 0 && proofs_ == observations_ && symbol_ &&
            !conflicting_;
    }

    std::size_t observationCount() const { return observations_; }
};

class CallSiteContractEvidence {
    typedef std::pair<
        const core::ir::Call *,
        std::shared_ptr<core::ir::calling::FunctionSignature>>
        PendingSignature;

    std::size_t observations_;
    std::size_t proofs_;
    const core::ir::calling::Convention *convention_;
    boost::optional<ByteSize> stackArgumentsSize_;
    bool conflicting_;
    std::vector<PendingSignature> signatures_;

public:
    CallSiteContractEvidence():
        observations_(0), proofs_(0), convention_(nullptr),
        conflicting_(false)
    {}

    void observe() { ++observations_; }

    void prove(
            const core::ir::Call *call,
            const core::ir::calling::Convention *convention,
            const boost::optional<ByteSize> &stackArgumentsSize,
            std::shared_ptr<core::ir::calling::FunctionSignature> signature =
                std::shared_ptr<core::ir::calling::FunctionSignature>()) {
        assert(call != nullptr);
        assert(convention != nullptr);
        ++proofs_;
        if (!convention_) {
            convention_ = convention;
            stackArgumentsSize_ = stackArgumentsSize;
        } else if (convention_ != convention ||
                   stackArgumentsSize_ != stackArgumentsSize)
        {
            conflicting_ = true;
        }
        signatures_.push_back(
            PendingSignature(call, std::move(signature)));
    }

    bool isProved() const {
        return observations_ != 0 && proofs_ == observations_ &&
            convention_ && !conflicting_;
    }

    std::size_t observationCount() const { return observations_; }

    void publish(core::Context &context, ByteAddr instructionAddress) const {
        assert(isProved());
        const core::ir::calling::CalleeId callSiteId{
            core::ir::calling::CallAddress(instructionAddress)};
        context.conventions()->setExternalConvention(
            callSiteId, convention_);
        context.conventions()->setExternalStackArgumentsSize(
            callSiteId, stackArgumentsSize_);
        for (const PendingSignature &pending : signatures_) {
            if (pending.second) {
                setCallSignature(context, pending.second, pending.first);
            }
        }
    }
};

/**
 * Removes the fallthrough following a proved noreturn call.
 *
 * \return True exactly when mutation happened, or would happen when
 *         \p allowProgramRefinement is false.
 */
bool terminateNoReturnCall(
        core::ir::Program &program, core::ir::Call *call,
        bool allowProgramRefinement) {
    if (!call || !call->instruction() || !call->basicBlock()) {
        return false;
    }

    const auto instruction = call->instruction();
    if (instruction->size() <= 0 ||
        instruction->addr() >
            (std::numeric_limits<ByteAddr>::max)() - instruction->size())
    {
        /* A continuation outside the representable address domain cannot be
         * matched to a fallthrough edge without signed overflow. */
        return false;
    }
    auto basicBlock = call->basicBlock();
    const ByteAddr continuationAddress =
        instruction->addr() + instruction->size();
    const bool continuationInsideBlock =
        continuationAddress !=
            (std::numeric_limits<ByteAddr>::max)() &&
        program.getBasicBlockCovering(continuationAddress) == basicBlock;
    auto continuation =
        program.getBasicBlockStartingAt(continuationAddress);

    if (continuationInsideBlock) {
        /* Program::createBasicBlock() cuts at the first statement belonging
         * to the continuation. If trailing bytes have no IR, it moves a
         * synthetic fallthrough jump instead. Reject a terminator which
         * would remain on the call side of the split. */
        bool splitMovesSuffix = false;
        foreach (const auto statement, basicBlock->statements()) {
            if (statement->instruction() &&
                statement->instruction()->addr() >= continuationAddress)
            {
                splitMovesSuffix = true;
                break;
            }
        }
        if (!splitMovesSuffix) {
            const auto jump = basicBlock->getJump();
            splitMovesSuffix = jump && !jump->instruction() &&
                jump->isUnconditional() &&
                jump->thenTarget().basicBlock();
        }
        if (!splitMovesSuffix && basicBlock->getTerminator()) {
            return false;
        }
    } else if (auto jump = basicBlock->getJump()) {
        /* Only an exact direct-successor edge is a call fallthrough. */
        if (jump->instruction() || !continuation ||
            !jump->isUnconditional() ||
            jump->thenTarget().basicBlock() != continuation)
        {
            return false;
        }
    } else if (const auto terminator = basicBlock->getTerminator()) {
        if (!terminator->is<core::ir::Halt>()) {
            return false;
        }
    }

    /* A canonical noreturn block contains Halt immediately after Call. Any
     * intervening statements are post-call effects (for example, x86 CALL's
     * synthetic stack restoration) and are unreachable too. */
    auto afterCall = basicBlock->statements().get_iterator(call);
    ++afterCall;
    bool alreadyTerminated = false;
    if (afterCall != basicBlock->statements().end()) {
        const auto next = *afterCall;
        ++afterCall;
        alreadyTerminated = next->is<core::ir::Halt>() &&
            afterCall == basicBlock->statements().end();
    }
    if (!continuationInsideBlock && alreadyTerminated) {
        return false;
    }

    if (!allowProgramRefinement) {
        return true;
    }

    if (continuationInsideBlock) {
        continuation = program.createBasicBlock(continuationAddress);
    }

    basicBlock = call->basicBlock();
    auto position = basicBlock->statements().get_iterator(call);
    ++position;
    while (position != basicBlock->statements().end()) {
        auto statement = *position;
        ++position;
        basicBlock->erase(statement);
    }
    basicBlock->pushBack(std::make_unique<core::ir::Halt>());
    return true;
}

bool applySymbolPrototypeSignatures(
        core::Context &context,
        const core::ir::calling::SymbolPrototypeRegistry &registry,
        bool allowProgramRefinement) {
    const auto architecture = context.image()->platform().architecture();
    const auto &dataflows = *context.dataflows();
    typedef core::ir::calling::SymbolPrototypeRecord Record;
    std::map<const Record *,
             std::shared_ptr<core::ir::calling::FunctionSignature>> signatures;
    std::map<ByteAddr, RecoveredCallback> callbacks;
    std::map<ByteAddr, NoReturnCallEvidence> noReturnEvidence;
    std::map<ByteAddr, CallSiteContractEvidence> callSiteEvidence;
    typedef std::pair<ByteAddr, std::size_t> CallbackEvidenceKey;
    std::map<CallbackEvidenceKey, CallbackCallEvidence> callbackEvidence;
    std::map<const core::image::Symbol *, bool> stableImportSymbols;
    bool programRefinementRequired = false;

    auto getSignature = [&](const Record *record) {
        auto &signature = signatures[record];
        if (!signature) {
            const auto convention = architecture->getCallingConvention(
                record->conventionName());
            if (convention &&
                hasConsistentPrototypeLayout(
                    *record, *convention, architecture->bitness()))
            {
                signature = makeFunctionSignature(*record, *convention);
            }
        }
        return signature;
    };

    for (const auto &functionAndDataflow : dataflows) {
        const auto function = functionAndDataflow.first;
        const auto &dataflow = *functionAndDataflow.second;
        foreach (const auto basicBlock, function->basicBlocks()) {
            foreach (const auto statement, basicBlock->statements()) {
                const auto call = statement->asCall();
                if (!call) {
                    continue;
                }

                NoReturnCallEvidence *lateNoReturnEvidence = nullptr;
                CallSiteContractEvidence *lateCallSiteEvidence = nullptr;
                if (call->instruction()) {
                    lateNoReturnEvidence = &noReturnEvidence[
                        call->instruction()->addr()];
                    lateNoReturnEvidence->observe();
                    lateCallSiteEvidence = &callSiteEvidence[
                        call->instruction()->addr()];
                    lateCallSiteEvidence->observe();
                }

                /* Every accepted path is backed by converged dataflow and an
                 * exact import origin (or an exact external direct target).
                 * Static opcode shape alone is not semantic evidence. */
                bool usesMutableImportSlot = false;
                const auto symbol = getImportedFunctionSymbol(
                    *context.image(), call, dataflow,
                    &usesMutableImportSlot);
                if (!symbol) {
                    continue;
                }
                if (usesMutableImportSlot) {
                    auto stability = stableImportSymbols.find(symbol);
                    if (stability == stableImportSymbols.end()) {
                        stability = stableImportSymbols.insert(
                            std::make_pair(
                                symbol,
                                isImportSymbolStableAcrossProgram(
                                    context, symbol))).first;
                    }
                    if (!stability->second) {
                        continue;
                    }
                }

                if (const auto record = getSymbolPrototype(
                        registry, *symbol)) {
                    const auto convention = architecture->getCallingConvention(
                        record->conventionName());
                    const auto signature = getSignature(record);
                    boost::optional<ByteSize> stackArgumentsSize;
                    const core::ir::calling::Convention *validatedConvention =
                        nullptr;
                    if (!signature || !signature->prototype() ||
                        !getPrototypeCallingConvention(
                            context, *record, validatedConvention,
                            stackArgumentsSize) ||
                        convention != validatedConvention ||
                        !lateCallSiteEvidence)
                    {
                        continue;
                    }

                    /* A resolved export address is not a unique ABI key: two
                     * import contracts can be forwarded to the same target.
                     * Keep authoritative prototype metadata on this call
                     * instruction so the next dataflow pass can override a
                     * coarse address-based guess without contaminating other
                     * call sites. */
                    lateCallSiteEvidence->prove(
                        call, convention, stackArgumentsSize, signature);
                    if (record->doesNotReturn() && lateNoReturnEvidence) {
                        /* Every Function clone of one Program call must agree.
                         * One unresolved or conflicting clone makes CFG
                         * pruning unsafe. */
                        lateNoReturnEvidence->prove(symbol);
                    }
                    const auto previousSignature =
                        context.signatures()->getSignature(call);
                    const auto &parameters =
                        signature->prototype()->parameters();
                    for (std::size_t index = 0;
                         index < parameters.size(); ++index) {
                        const auto &callback =
                            parameters[index].callbackPrototype();
                        if (!callback) {
                            continue;
                        }

                        if (const auto address = getConcreteCallArgument(
                                call, dataflow, *context.hooks(),
                                previousSignature.get(), index,
                                *convention,
                                parameters[index].type().size()))
                        {
                            callbackEvidence[CallbackEvidenceKey(
                                call->instruction()->addr(), index)].prove(
                                    *address, callback);
                        }
                    }
                } else if (lateCallSiteEvidence) {
                    /* Microsoft x86 decoration is binary ABI evidence, but
                     * attach it only after the same converged import-origin
                     * proof used for catalog contracts. */
                    const core::ir::calling::Convention *convention = nullptr;
                    boost::optional<ByteSize> stackArgumentsSize;
                    if (getDecoratedImportCallingConvention(
                            context, *symbol, convention,
                            stackArgumentsSize))
                    {
                        lateCallSiteEvidence->prove(
                            call, convention, stackArgumentsSize);
                    }
                }
            }
        }
    }

    for (const auto &addressAndEvidence : callSiteEvidence) {
        if (addressAndEvidence.second.isProved()) {
            addressAndEvidence.second.publish(
                context, addressAndEvidence.first);
        }
    }


    for (const auto &keyAndEvidence : callbackEvidence) {
        const auto callSite = callSiteEvidence.find(
            keyAndEvidence.first.first);
        if (callSite != callSiteEvidence.end() &&
            callSite->second.isProved() &&
            keyAndEvidence.second.isProved(
                callSite->second.observationCount()))
        {
            keyAndEvidence.second.publish(callbacks);
        }
    }

    std::map<QString, std::size_t> hintUseCounts;
    for (const auto &addressAndCallback : callbacks) {
        const RecoveredCallback &recovered = addressAndCallback.second;
        if (!recovered.conflictingPrototype && recovered.prototype &&
            !recovered.prototype->preferredName().isEmpty())
        {
            const QString hint = recovered.prototype->preferredName();
            ++hintUseCounts[hint.toLower()];
        }
    }

    for (const auto &addressAndCallback : callbacks) {
        const ByteAddr address = addressAndCallback.first;
        const RecoveredCallback &recovered = addressAndCallback.second;
        if (recovered.conflictingPrototype || !recovered.prototype) {
            continue;
        }

        const auto convention = getCallbackConvention(
            context, *recovered.prototype);
        if (!convention ||
            !isTrustedLocalFunctionEntry(context, address))
        {
            continue;
        }

        auto program = context.program();
        if (!program->isFunctionEntry(address)) {
            programRefinementRequired = true;
            if (allowProgramRefinement) {
                /* Splitting is safe because validation above requires an
                 * exact decoded instruction start. Functions and every
                 * pointer-keyed analysis are rebuilt by MasterAnalyzer. */
                program->refineFunctionEntry(address);
            }
            /* Current Functions are clones of the pre-refinement Program.
             * Never attach a callback contract to one of those stale owners,
             * including on the non-mutating final iteration. */
            continue;
        }

        auto function = getFunctionAtAddress(context, address);
        if (!function) {
            continue;
        }
        const QString preferredName = getCallbackPreferredName(
            context, address, *recovered.prototype, hintUseCounts);
        const auto signature = makeCallbackSignature(
            *recovered.prototype, preferredName, *convention);
        if (!signature) {
            continue;
        }

        const core::ir::calling::CalleeId calleeId{
            core::ir::calling::EntryAddress(address)};
        context.conventions()->setExternalConvention(calleeId, convention);
        const boost::optional<ByteSize> stackArgumentsSize =
            recovered.prototype->variadic() ? boost::optional<ByteSize>() :
            getCallbackStackArgumentsSize(
                *recovered.prototype, *convention);
        /* A fixed cdecl callback has an authoritative fixed argument extent
         * even though the caller performs cleanup. Unknown and variadic
         * layouts explicitly mask any persistent size. */
        context.conventions()->setExternalStackArgumentsSize(
            calleeId, stackArgumentsSize);
        setFunctionSignature(
            context, calleeId, signature, function);
    }

    /* A callback discovered above may have split a Function in the Program.
     * The current Functions/dataflows then predate that boundary and may be
     * missing a new overlapping clone. Restart first and only prune a
     * noreturn edge after every clone in the rebuilt ownership graph agrees. */
    if (!programRefinementRequired) {
        auto program = context.program();
        for (const auto &addressAndEvidence : noReturnEvidence) {
            if (!addressAndEvidence.second.isProved()) {
                continue;
            }
            auto call = findProgramCallAt(
                *program, addressAndEvidence.first);
            if (terminateNoReturnCall(
                    *program, call, allowProgramRefinement))
            {
                programRefinementRequired = true;
            }
        }
    }

    return programRefinementRequired;
}

} // anonymous namespace

void X86MasterAnalyzer::createProgram(core::Context &context) const {
    MasterAnalyzer::createProgram(context);

    /*
     * Patch the IR to implement x86-64 implicit zero extend.
     */
    if (context.image()->platform().architecture()->bitness() == 64) {
        auto minDomain = X86Registers::rax()->memoryLocation().domain();
        auto maxDomain = X86Registers::r15()->memoryLocation().domain();

        auto program = const_cast<core::ir::Program *>(context.program());

        foreach (auto *basicBlock, program->basicBlocks()) {
            context.cancellationToken().poll();

            foreach (auto statement, basicBlock->statements()) {
                if (auto assignment = statement->asAssignment()) {
                    if (auto access = assignment->left()->asMemoryLocationAccess()) {
                        if (minDomain <= access->memoryLocation().domain() &&
                            access->memoryLocation().domain() <= maxDomain &&
                            access->memoryLocation().addr() == 0 &&
                            access->memoryLocation().size() == 32)
                        {
                            auto patch = std::make_unique<core::ir::Assignment>(
                                    std::make_unique<core::ir::MemoryLocationAccess>(access->memoryLocation().shifted(32)),
                                    std::make_unique<core::ir::Constant>(SizedValue(32, 0)));
                            patch->setInstruction(statement->instruction());

                            basicBlock->insertAfter(statement, std::move(patch));
                        }
                    }
                }
            }
        }
    }
}

void X86MasterAnalyzer::detectCallingConventions(core::Context &context) const {
    context.logToken().info(tr("Detecting calling conventions."));

    auto architecture = context.image()->platform().architecture();
    const bool isWindows =
        context.image()->platform().operatingSystem() ==
        core::image::Platform::Windows;

    if (architecture->bitness() == 32 || architecture->bitness() == 64)
    {
        addImportThunkAliases(context);
    }

    if (isWindows &&
        (architecture->bitness() == 32 || architecture->bitness() == 64))
    {
        using core::ir::calling::CalleeId;
        using core::ir::calling::EntryAddress;

        foreach (auto symbol, context.image()->symbols()) {
            if (!symbol->value() ||
                *symbol->value() > static_cast<ConstantValue>(
                    (std::numeric_limits<ByteAddr>::max)()) ||
                symbol->type() != core::image::SymbolType::FUNCTION)
            {
                continue;
            }

            const CalleeId calleeId(EntryAddress(
                static_cast<ByteAddr>(*symbol->value())));
            const auto externalSymbol = getImportedFunctionSymbol(
                *context.image(), calleeId);
            if (externalSymbol) {
                /* This entry is a relocation-proved external forwarding
                 * boundary. Its tail jump is not a local return path and
                 * therefore supplies no return-stack-cleanup evidence. */
                context.conventions()->setExternalBodyOpaque(calleeId);
            }
        }
    }

    if (architecture->bitness() == 32) {
        using core::ir::calling::CalleeId;
        using core::ir::calling::EntryAddress;

        if (isWindows) {
            auto stdcall32 = architecture->getCallingConvention(
                QLatin1String("stdcall32"));

            foreach (auto symbol, context.image()->symbols()) {
                if (!symbol->value() ||
                    *symbol->value() > static_cast<ConstantValue>(
                        (std::numeric_limits<ByteAddr>::max)()) ||
                    symbol->type() != core::image::SymbolType::FUNCTION)
                {
                    continue;
                }
                CalleeId calleeId(EntryAddress(
                    static_cast<ByteAddr>(*symbol->value())));
                if (getImportedFunctionSymbol(
                        *context.image(), calleeId))
                {
                    /* Import contracts are call-site facts until converged
                     * dataflow proves the mutable slot still has that origin. */
                    continue;
                }
                if (context.conventions()->getConvention(calleeId)) {
                    continue;
                }
                if (setExplicitThiscallConvention(
                        context, calleeId, symbol->name()))
                {
                    continue;
                }
                const auto argumentsSize =
                    getStdcallStackArgumentsSize(symbol->name());
                if (!argumentsSize) {
                    continue;
                }

                /* Do not let an alias overwrite convention metadata already seen. */
                const auto existingConvention =
                    context.conventions()->getConvention(calleeId);
                if (existingConvention && existingConvention != stdcall32) {
                    continue;
                }
                if (!existingConvention) {
                    context.conventions()->setConvention(calleeId, stdcall32);
                }
                if (!context.conventions()->getStackArgumentsSize(calleeId)) {
                    context.conventions()->setStackArgumentsSize(
                        calleeId, *argumentsSize);
                }
            }
        }

    }

    /*
     * A return immediate is an execution effect, not a calling-convention
     * name. Collect it for every supported x86 word size. In particular,
     * RET and RET 0 are exact zero effects; they are not missing evidence.
     */
    if (architecture->bitness() == 16 || architecture->bitness() == 32 ||
        architecture->bitness() == 64)
    {
        using core::ir::calling::CalleeId;
        using core::ir::calling::EntryAddress;

        ud_t ud_obj_;
        ud_init(&ud_obj_);
        ud_set_mode(&ud_obj_, context.image()->platform().architecture()->bitness());

        foreach (auto function, context.functions()->list()) {
            context.cancellationToken().poll();
            if (!function->entry() || !function->entry()->address()) {
                continue;
            }

            CalleeId calleeId(
                EntryAddress(*function->entry()->address()));
            /* The phase is normally single-shot, but keeping the analysis
             * idempotent prevents stale body facts after an IR rebuild. */
            context.conventions()->clearReturnStackCleanup(calleeId);

            boost::optional<ByteSize> calleeCleanupSize;
            bool sawReturn = false;
            bool inconsistentCleanup = false;
            foreach (auto basicBlock, function->basicBlocks()) {
                auto terminator = basicBlock->getTerminator();
                const X86Instruction *instruction = terminator ?
                    checked_cast<const X86Instruction *>(
                        terminator->instruction()) : nullptr;
                bool isReturn = false;
                if (instruction) {
                    ud_set_pc(&ud_obj_, instruction->addr());
                    ud_set_input_buffer(
                        &ud_obj_, const_cast<uint8_t *>(instruction->bytes()),
                        checked_cast<std::size_t>(instruction->size()));
                    const unsigned int decodedSize = ud_disassemble(&ud_obj_);
                    isReturn =
                        decodedSize == static_cast<unsigned int>(
                            instruction->size()) &&
                        ud_obj_.mnemonic == UD_Iret;
                }

                if (isReturn) {
                    sawReturn = true;
                    ByteSize cleanupSize = 0;
                    if (ud_obj_.operand[0].type == UD_OP_IMM &&
                        ud_obj_.operand[0].size == 16)
                    {
                        cleanupSize = ud_obj_.operand[0].lval.uword;
                    } else if (ud_obj_.operand[0].type != UD_NONE) {
                        inconsistentCleanup = true;
                        break;
                    }

                    if (calleeCleanupSize &&
                        *calleeCleanupSize != cleanupSize)
                    {
                        inconsistentCleanup = true;
                        break;
                    }
                    calleeCleanupSize = cleanupSize;
                    continue;
                }

                /* A halt has no returning path, so it contributes no cleanup
                 * value. Other exits must be proved internal; a tail jump or
                 * an unresolved/fall-through exit can return through another
                 * ABI and therefore conflicts with a synthesized exact SP. */
                if (terminator && terminator->is<core::ir::Halt>()) {
                    continue;
                }

                const core::ir::Jump *jump = basicBlock->getJump();
                auto targetLeavesFunction = [function](
                        const core::ir::JumpTarget &target) {
                    if (target.basicBlock()) {
                        return target.basicBlock()->function() != function;
                    }
                    if (target.table()) {
                        if (target.table()->empty()) {
                            return true;
                        }
                        foreach (const core::ir::JumpTableEntry &entry,
                                 *target.table()) {
                            if (!entry.basicBlock() ||
                                entry.basicBlock()->function() != function)
                            {
                                return true;
                            }
                        }
                        return false;
                    }
                    /* A required jump target with no in-function block is an
                     * unresolved/external exit even if cloning discarded its
                     * original address expression. */
                    return true;
                };

                if (!jump || targetLeavesFunction(jump->thenTarget()) ||
                    (jump->isConditional() &&
                     targetLeavesFunction(jump->elseTarget())))
                {
                    inconsistentCleanup = true;
                    break;
                }
            }

            if (inconsistentCleanup || !sawReturn || !calleeCleanupSize) {
                if (inconsistentCleanup) {
                    context.conventions()->setConflictingReturnStackCleanup(
                        calleeId);
                }
                continue;
            }

            /*
             * RET N proves the runtime stack effect and its byte count, but
             * not whether register arguments make this stdcall, thiscall,
             * fastcall, or another ABI. Store that effect independently so a
             * provider-supplied argument layout is never discarded merely
             * because its default cleanup policy disagrees.
             */
            context.conventions()->setReturnStackCleanupSize(
                calleeId, *calleeCleanupSize);
        }
    }
}

void X86MasterAnalyzer::detectCallingConvention(core::Context &context, const core::ir::calling::CalleeId &calleeId) const {
    const auto &platform = context.image()->platform();
    auto architecture = platform.architecture();

    if ((architecture->bitness() == 32 || architecture->bitness() == 64) &&
        platform.operatingSystem() == core::image::Platform::Windows)
    {
        if (getImportedFunctionSymbol(*context.image(), calleeId)) {
            /* A statically identified import target can have a local forwarding thunk,
             * but that thunk has no implementation-side parameter reads.
             * Preserve the boundary while allowing independent call-frame
             * evidence to describe caller-cleanup calls. */
            context.conventions()->setExternalBodyOpaque(calleeId);

            /* Provider contracts are installed only after converged def-use
             * proves that this particular call still reaches the imported
             * slot. Installing them here would turn an opcode/relocation
             * guess made during provisional dataflow into persistent ABI
             * state, even when the program visibly overwrote the IAT entry. */
        }
    }

    auto setConvention = [&](const char *name) {
        context.conventions()->setFallbackConvention(
            calleeId,
            architecture->getCallingConvention(QLatin1String(name)));
    };

    switch (architecture->bitness()) {
        case 16:
            setConvention("cdecl16");
            break;
        case 32:
            setConvention("cdecl32");
            break;
        case 64:
            if (platform.operatingSystem() == core::image::Platform::Windows) {
                setConvention("microsoft64");
            } else {
                setConvention("amd64");
            }
            break;
    }
}

bool X86MasterAnalyzer::applyExternalSignatures(
        core::Context &context,
        bool allowProgramRefinement) const {
    const auto &platform = context.image()->platform();
    const auto bitness = platform.architecture()->bitness();
    if (platform.operatingSystem() == core::image::Platform::Windows &&
        (bitness == 32 || bitness == 64))
    {
        const auto &registry = getPrototypeRegistry(context);
        return applySymbolPrototypeSignatures(
            context, registry, allowProgramRefinement);
    }
    return false;
}

} // namespace x86
} // namespace arch
} // namespace nc

/* vim:set et sts=4 sw=4: */
