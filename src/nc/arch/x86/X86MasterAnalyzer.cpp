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

QString canonicalWindowsDebuggerSymbolName(QString name) {
    name = name.trimmed();

    if (name.size() >= 2 && name.startsWith(QLatin1Char('<')) &&
        name.endsWith(QLatin1Char('>')))
    {
        name = name.mid(1, name.size() - 2);
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

core::ir::calling::SymbolPrototypeRegistry makePrototypeRegistry(
        const core::Context &context) {
    core::ir::calling::SymbolPrototypeRegistry registry;
    const core::ir::calling::SymbolPrototypeTarget target(
        QLatin1String("x86"),
        operatingSystemName(context.image()->platform().operatingSystem()),
        context.image()->platform().architecture()->bitness());

    for (const auto &provider : context.symbolPrototypeProviders()) {
        if (provider) {
            registry.addProvider(*provider, target);
        }
    }
    return registry;
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
        relocation->size() == bitness / CHAR_BIT &&
        relocation->symbol()->type() == core::image::SymbolType::FUNCTION)
    {
        return relocation->symbol();
    }
    return nullptr;
}

/* Resolve a decoded indirect call/jump whose static memory operand is an import slot. */
const core::image::Symbol *getIndirectImport(const core::image::Image &image,
                                             ByteAddr instructionAddress,
                                             X86Instruction::ControlTransferKind kind) {
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

    return getImportSymbolAtSlot(image, slot);
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
        if (symbol && symbol->type() == core::image::SymbolType::FUNCTION) {
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
                                                     const core::ir::Call *call) {
    assert(call != nullptr);

    /* The import relocation names the contract selected by this call. Prefer
     * it to a resolved target address, which may point at a forwarded export
     * in a different module with different or missing debugger metadata. */
    if (call->instruction()) {
        const auto symbol = getIndirectImport(
            image, call->instruction()->addr(),
            X86Instruction::ControlTransferKind::CALL);
        if (symbol) {
            return symbol;
        }
    }

    if (const auto target = call->target()->asConstant()) {
        const ConstantValue targetValue = target->value().value();
        if (targetValue <= static_cast<ConstantValue>(
                (std::numeric_limits<ByteAddr>::max)()))
        {
            const core::ir::calling::CalleeId calleeId(
                core::ir::calling::EntryAddress(
                    static_cast<ByteAddr>(targetValue)));
            if (const auto symbol = getImportedFunctionSymbol(image, calleeId)) {
                return symbol;
            }
        }
    }

    return nullptr;
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

bool setPrototypeCallingConvention(
        core::Context &context,
        const core::ir::calling::CalleeId &calleeId,
        const core::ir::calling::SymbolPrototypeRecord &record) {
    const auto convention =
        context.image()->platform().architecture()->getCallingConvention(
            record.conventionName());
    if (!convention) {
        return false;
    }

    context.conventions()->setConvention(calleeId, convention);
    if (record.stackArgumentsSize()) {
        context.conventions()->setStackArgumentsSize(
            calleeId, *record.stackArgumentsSize());
    }
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
    if (!argumentsSize || *argumentsSize < 0 || *argumentsSize % 4 != 0) {
        return boost::none;
    }
    return argumentsSize;
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
            callback.memoryEffectsAreComplete()));

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
        context.signatures()->setSignature(*calleeId.entryAddress(), signature);
    }
    if (function) {
        context.signatures()->setSignature(function, signature);
    }
}

void setCallSignature(core::Context &context,
                      const std::shared_ptr<core::ir::calling::FunctionSignature> &functionSignature,
                      const core::ir::Call *call) {
    auto callSignature = std::make_shared<core::ir::calling::CallSignature>();

    callSignature->arguments() = functionSignature->arguments();
    callSignature->setReturnValue(functionSignature->returnValue());
    callSignature->setPrototype(functionSignature->prototype());
    context.signatures()->setSignature(call, callSignature);
}

bool areCompatibleTypes(
        const core::ir::calling::TypeDescription &left,
        const core::ir::calling::TypeDescription &right) {
    return left.kind() == right.kind() && left.size() == right.size() &&
           left.isUnsigned() == right.isUnsigned();
}

typedef std::pair<
    const core::ir::calling::FunctionPrototype *,
    const core::ir::calling::FunctionPrototype *> PrototypePair;

struct PrototypePairLess {
    bool operator()(const PrototypePair &left,
                    const PrototypePair &right) const {
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

bool areCompatiblePrototypes(
        const core::ir::calling::FunctionPrototype &left,
        const core::ir::calling::FunctionPrototype &right,
        std::set<PrototypePair, PrototypePairLess> &visited) {
    if (&left == &right) {
        return true;
    }

    const auto pair = std::make_pair(&left, &right);
    if (!visited.insert(pair).second) {
        return true;
    }

    if (!areCompatibleTypes(left.returnType(), right.returnType()) ||
        left.callingConvention() != right.callingConvention() ||
        left.parameters().size() != right.parameters().size())
    {
        return false;
    }

    for (std::size_t index = 0; index < left.parameters().size(); ++index) {
        const auto &leftParameter = left.parameters()[index];
        const auto &rightParameter = right.parameters()[index];
        if (!areCompatibleTypes(leftParameter.type(), rightParameter.type()) ||
            leftParameter.pointeeAccess() !=
                rightParameter.pointeeAccess())
        {
            return false;
        }

        const auto &leftCallback = leftParameter.callbackPrototype();
        const auto &rightCallback = rightParameter.callbackPrototype();
        if (static_cast<bool>(leftCallback) !=
            static_cast<bool>(rightCallback))
        {
            return false;
        }
        if (leftCallback && !areCompatiblePrototypes(
                *leftCallback, *rightCallback, visited))
        {
            return false;
        }
    }
    return true;
}

bool areCompatiblePrototypes(
        const core::ir::calling::FunctionPrototype &left,
        const core::ir::calling::FunctionPrototype &right) {
    std::set<PrototypePair, PrototypePairLess> visited;
    return areCompatiblePrototypes(left, right, visited);
}

struct RecoveredCallback {
    std::shared_ptr<const core::ir::calling::FunctionPrototype> prototype;
    bool conflictingPrototype;

    RecoveredCallback(): conflictingPrototype(false) {}

    void merge(const std::shared_ptr<const core::ir::calling::FunctionPrototype>
                   &candidate) {
        assert(candidate != nullptr);
        if (!prototype) {
            prototype = candidate;
        } else if (!areCompatiblePrototypes(*prototype, *candidate)) {
            conflictingPrototype = true;
        }
    }
};

const core::ir::calling::Convention *getCallbackConvention(
        const core::Context &context,
        const core::ir::calling::FunctionPrototype &callback,
        SmallBitSize bitness) {
    const auto architecture = context.image()->platform().architecture();
    if (bitness == 64) {
        return architecture->getCallingConvention(
            QLatin1String("microsoft64"));
    }
    if (bitness != 32) {
        return nullptr;
    }

    const QString &declaration = callback.callingConvention();
    if (declaration == QLatin1String("__stdcall")) {
        return architecture->getCallingConvention(QLatin1String("stdcall32"));
    }
    if (declaration == QLatin1String("__thiscall")) {
        return architecture->getCallingConvention(QLatin1String("thiscall32"));
    }
    if (declaration.isEmpty() || declaration == QLatin1String("__cdecl")) {
        return architecture->getCallingConvention(QLatin1String("cdecl32"));
    }
    return nullptr;
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

void applySymbolPrototypeSignatures(
        core::Context &context,
        const core::ir::calling::SymbolPrototypeRegistry &registry) {
    const auto architecture = context.image()->platform().architecture();
    const auto bitness = architecture->bitness();
    const auto &dataflows = *context.dataflows();
    typedef core::ir::calling::SymbolPrototypeRecord Record;
    std::map<const Record *,
             std::shared_ptr<core::ir::calling::FunctionSignature>> signatures;
    std::map<ByteAddr, RecoveredCallback> callbacks;

    auto getSignature = [&](const Record *record) {
        auto &signature = signatures[record];
        if (!signature) {
            const auto convention = architecture->getCallingConvention(
                record->conventionName());
            if (convention) {
                signature = makeFunctionSignature(*record, *convention);
            }
        }
        return signature;
    };

    for (const auto &functionAndDataflow : dataflows) {
        const auto function = functionAndDataflow.first;
        const auto &dataflow = *functionAndDataflow.second;
        const auto functionId = core::ir::calling::getCalleeId(function);

        if (const auto symbol = getImportedFunctionSymbol(*context.image(), functionId)) {
            if (const auto record = getSymbolPrototype(registry, *symbol)) {
                if (const auto signature = getSignature(record)) {
                    setFunctionSignature(
                        context, functionId, signature, function);
                }
            }
        }

        foreach (const auto basicBlock, function->basicBlocks()) {
            foreach (const auto statement, basicBlock->statements()) {
                const auto call = statement->asCall();
                if (!call) {
                    continue;
                }

                /* Select the call-site IAT contract before a possibly
                 * forwarded resolved target. */
                const auto symbol =
                    getImportedFunctionSymbol(*context.image(), call);
                if (!symbol) {
                    continue;
                }

                if (const auto record = getSymbolPrototype(
                        registry, *symbol))
                {
                    const auto convention = architecture->getCallingConvention(
                        record->conventionName());
                    const auto signature = getSignature(record);
                    if (!convention || !signature || !signature->prototype()) {
                        continue;
                    }

                    /* A resolved export address is not a unique ABI key: two
                     * import contracts can be forwarded to the same target.
                     * Keep authoritative prototype metadata on this call
                     * instruction so the next dataflow pass can override a
                     * coarse address-based guess without contaminating other
                     * call sites. */
                    if (call->instruction()) {
                        const core::ir::calling::CalleeId callSiteId(
                            core::ir::calling::CallAddress(
                                call->instruction()->addr()));
                        if (!setPrototypeCallingConvention(
                                context, callSiteId, *record))
                        {
                            continue;
                        }
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
                            callbacks[*address].merge(callback);
                        }
                    }
                    setCallSignature(context, signature, call);
                }
            }
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

        auto function = getFunctionAtAddress(context, address);
        const auto convention = getCallbackConvention(
            context, *recovered.prototype, bitness);
        if (!function || !convention) {
            continue;
        }
        const auto existingSignature =
            context.signatures()->getSignature(function);
        if (existingSignature && existingSignature->prototype()) {
            /* Do not replace stronger metadata already attached to a symbol. */
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
        context.conventions()->setConvention(calleeId, convention);
        if (convention->calleeCleanup()) {
            if (const auto stackArgumentsSize =
                getCallbackStackArgumentsSize(
                        *recovered.prototype, *convention))
            {
                context.conventions()->setStackArgumentsSize(
                    calleeId, *stackArgumentsSize);
            }
        }
        setFunctionSignature(
            context, calleeId, signature, function);
    }
}

void terminateNoReturnCalls(
        core::Context &context,
        const core::ir::calling::SymbolPrototypeRegistry &registry) {
    auto program = const_cast<core::ir::Program *>(context.program());
    std::vector<core::ir::Call *> noReturnCalls;

    foreach (const auto basicBlock, program->basicBlocks()) {
        foreach (const auto statement, basicBlock->statements()) {
            const auto call = statement->as<core::ir::Call>();
            if (!call) {
                continue;
            }

            const auto symbol = getImportedFunctionSymbol(*context.image(), call);
            const auto record = symbol ?
                getSymbolPrototype(registry, *symbol) : nullptr;
            if (record && record->doesNotReturn()) {
                noReturnCalls.push_back(call);
            }
        }
    }

    foreach (const auto call, noReturnCalls) {
        const auto instruction = call->instruction();
        auto basicBlock = call->basicBlock();
        if (!instruction || !basicBlock) {
            continue;
        }

        /* Move instructions after the call into a disconnected block. */
        const ByteAddr continuationAddress = instruction->endAddr();
        auto continuation = program->getBasicBlockStartingAt(continuationAddress);
        if (program->getBasicBlockCovering(continuationAddress) == basicBlock) {
            continuation = program->createBasicBlock(continuationAddress);
        }

        basicBlock = call->basicBlock();
        if (auto jump = basicBlock->getJump()) {
            /* Only remove the fallthrough edge emitted by IRGenerator. */
            if (!continuation || !jump->isUnconditional() ||
                jump->thenTarget().basicBlock() != continuation)
            {
                continue;
            }
            basicBlock->erase(jump);
        }
        if (!basicBlock->getTerminator()) {
            basicBlock->pushBack(std::make_unique<core::ir::Halt>());
        }
    }
}

} // anonymous namespace

void X86MasterAnalyzer::createProgram(core::Context &context) const {
    MasterAnalyzer::createProgram(context);

    const auto &platform = context.image()->platform();
    if (platform.operatingSystem() == core::image::Platform::Windows &&
        (platform.architecture()->bitness() == 32 || platform.architecture()->bitness() == 64))
    {
        const auto registry = makePrototypeRegistry(context);
        terminateNoReturnCalls(context, registry);
    }

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

        const auto registry = makePrototypeRegistry(context);
        foreach (auto symbol, context.image()->symbols()) {
            if (!symbol->value() ||
                symbol->type() != core::image::SymbolType::FUNCTION)
            {
                continue;
            }

            const CalleeId calleeId(EntryAddress(*symbol->value()));
            const auto externalSymbol = getImportedFunctionSymbol(
                *context.image(), calleeId);
            const auto record = externalSymbol ?
                getSymbolPrototype(registry, *externalSymbol) : nullptr;
            if (record) {
                setPrototypeCallingConvention(context, calleeId, *record);
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
                    symbol->type() != core::image::SymbolType::FUNCTION)
                {
                    continue;
                }
                CalleeId calleeId(EntryAddress(*symbol->value()));
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
        if (auto symbol = getImportedFunctionSymbol(*context.image(), calleeId)) {
            const auto registry = makePrototypeRegistry(context);
            if (const auto record = getSymbolPrototype(
                    registry, *symbol))
            {
                if (setPrototypeCallingConvention(
                        context, calleeId, *record))
                {
                    return;
                }
            }
            if (architecture->bitness() == 32 &&
                setExplicitThiscallConvention(
                    context, calleeId, symbol->name()))
            {
                return;
            }
        }
    }

    auto setConvention = [&](const char *name) {
        context.conventions()->setConvention(calleeId, architecture->getCallingConvention(QLatin1String(name)));
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

void X86MasterAnalyzer::reconstructSignatures(core::Context &context) const {
    MasterAnalyzer::reconstructSignatures(context);

    const auto &platform = context.image()->platform();
    const auto bitness = platform.architecture()->bitness();
    if (platform.operatingSystem() == core::image::Platform::Windows &&
        (bitness == 32 || bitness == 64))
    {
        const auto registry = makePrototypeRegistry(context);
        applySymbolPrototypeSignatures(context, registry);
    }
}

} // namespace x86
} // namespace arch
} // namespace nc

/* vim:set et sts=4 sw=4: */
