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
#include <cstdint>
#include <cstring>
#include <limits>
#include <map>
#include <set>
#include <vector>

#include <boost/optional.hpp>

#include <nc/common/Foreach.h>
#include <nc/common/StringToInt.h>
#include <nc/common/Unreachable.h>
#include <nc/common/make_unique.h>

#include <nc/core/Context.h>
#include <nc/core/arch/Capstone.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Relocation.h>
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
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/FunctionSignature.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/Signatures.h>
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

enum ApiResultKind {
    API_RESULT_VOID,
    API_RESULT_INT32,
    API_RESULT_POINTER_SIZED
};

enum ApiTypeKind {
    API_TYPE_VOID,
    API_TYPE_INT32,
    API_TYPE_UINT32,
    API_TYPE_INTPTR,
    API_TYPE_UINTPTR,
    API_TYPE_POINTER
};

struct KnownApiType {
    ApiTypeKind kind;
    const char *name;
};

struct KnownApiParameter {
    KnownApiType type;
    const char *name;
    bool mayWriteMemory;
};

struct KnownWin32Api {
    const char *name;
    std::size_t argumentCount;
    unsigned int int32ArgumentMask;
    ApiResultKind resultKind;
    bool doesNotReturn;
    KnownApiType returnType;
    const KnownApiParameter *parameters;
};

const KnownApiParameter DIALOG_BOX_PARAM_A_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HINSTANCE"}, "hInstance", false},
    {{API_TYPE_POINTER, "LPCSTR"}, "lpTemplateName", false},
    {{API_TYPE_POINTER, "HWND"}, "hWndParent", false},
    {{API_TYPE_POINTER, "DLGPROC"}, "lpDialogFunc", false},
    {{API_TYPE_INTPTR, "LPARAM"}, "dwInitParam", true}
};

const KnownApiParameter DIALOG_BOX_PARAM_W_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HINSTANCE"}, "hInstance", false},
    {{API_TYPE_POINTER, "LPCWSTR"}, "lpTemplateName", false},
    {{API_TYPE_POINTER, "HWND"}, "hWndParent", false},
    {{API_TYPE_POINTER, "DLGPROC"}, "lpDialogFunc", false},
    {{API_TYPE_INTPTR, "LPARAM"}, "dwInitParam", true}
};

const KnownApiParameter END_DIALOG_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hDlg", false},
    {{API_TYPE_INTPTR, "INT_PTR"}, "nResult", false}
};

const KnownApiParameter EXIT_PROCESS_PARAMETERS[] = {
    {{API_TYPE_UINT32, "UINT"}, "uExitCode", false}
};

const KnownApiParameter GET_DLG_ITEM_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hDlg", false},
    {{API_TYPE_INT32, "int"}, "nIDDlgItem", false}
};

const KnownApiParameter GET_DLG_ITEM_TEXT_A_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hDlg", false},
    {{API_TYPE_INT32, "int"}, "nIDDlgItem", false},
    {{API_TYPE_POINTER, "LPSTR"}, "lpString", true},
    {{API_TYPE_INT32, "int"}, "cchMax", false}
};

const KnownApiParameter GET_DLG_ITEM_TEXT_W_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hDlg", false},
    {{API_TYPE_INT32, "int"}, "nIDDlgItem", false},
    {{API_TYPE_POINTER, "LPWSTR"}, "lpString", true},
    {{API_TYPE_INT32, "int"}, "cchMax", false}
};

const KnownApiParameter GET_MODULE_HANDLE_A_PARAMETERS[] = {
    {{API_TYPE_POINTER, "LPCSTR"}, "lpModuleName", false}
};

const KnownApiParameter GET_MODULE_HANDLE_W_PARAMETERS[] = {
    {{API_TYPE_POINTER, "LPCWSTR"}, "lpModuleName", false}
};

const KnownApiParameter LOAD_ICON_A_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HINSTANCE"}, "hInstance", false},
    {{API_TYPE_POINTER, "LPCSTR"}, "lpIconName", false}
};

const KnownApiParameter LOAD_ICON_W_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HINSTANCE"}, "hInstance", false},
    {{API_TYPE_POINTER, "LPCWSTR"}, "lpIconName", false}
};

const KnownApiParameter MESSAGE_BOX_A_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hWnd", false},
    {{API_TYPE_POINTER, "LPCSTR"}, "lpText", false},
    {{API_TYPE_POINTER, "LPCSTR"}, "lpCaption", false},
    {{API_TYPE_UINT32, "UINT"}, "uType", false}
};

const KnownApiParameter MESSAGE_BOX_W_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hWnd", false},
    {{API_TYPE_POINTER, "LPCWSTR"}, "lpText", false},
    {{API_TYPE_POINTER, "LPCWSTR"}, "lpCaption", false},
    {{API_TYPE_UINT32, "UINT"}, "uType", false}
};

const KnownApiParameter SEND_MESSAGE_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hWnd", false},
    {{API_TYPE_UINT32, "UINT"}, "Msg", false},
    {{API_TYPE_UINTPTR, "WPARAM"}, "wParam", true},
    {{API_TYPE_INTPTR, "LPARAM"}, "lParam", true}
};

const KnownApiParameter SET_FOCUS_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hWnd", false}
};

const KnownApiParameter LSTRLEN_A_PARAMETERS[] = {
    {{API_TYPE_POINTER, "LPCSTR"}, "lpString", false}
};

const KnownApiParameter LSTRLEN_W_PARAMETERS[] = {
    {{API_TYPE_POINTER, "LPCWSTR"}, "lpString", false}
};

const KnownApiParameter DIALOG_PROCEDURE_PARAMETERS[] = {
    {{API_TYPE_POINTER, "HWND"}, "hWnd", false},
    {{API_TYPE_UINT32, "UINT"}, "uMsg", false},
    {{API_TYPE_UINTPTR, "WPARAM"}, "wParam", true},
    {{API_TYPE_INTPTR, "LPARAM"}, "lParam", true}
};

/*
 * PE import names normally do not carry the @N suffix which the generic
 * stdcall detector below relies on. Keep the small amount of API knowledge
 * needed by the analyzer in one table, so adding another prototype does not
 * require changing the calling-convention logic.
 */
const KnownWin32Api KNOWN_WIN32_APIS[] = {
    /* name, argc, 32-bit argument mask, result, noreturn, source return type, parameters */
    {"DialogBoxParamA",  5, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_INTPTR, "INT_PTR"}, DIALOG_BOX_PARAM_A_PARAMETERS},
    {"DialogBoxParamW",  5, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_INTPTR, "INT_PTR"}, DIALOG_BOX_PARAM_W_PARAMETERS},
    {"EndDialog",        2, 0x00, API_RESULT_INT32, false,
        {API_TYPE_INT32, "BOOL"}, END_DIALOG_PARAMETERS},
    {"ExitProcess",      1, 0x01, API_RESULT_VOID, true,
        {API_TYPE_VOID, "void"}, EXIT_PROCESS_PARAMETERS},
    {"GetDlgItem",       2, 0x02, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_POINTER, "HWND"}, GET_DLG_ITEM_PARAMETERS},
    {"GetDlgItemTextA",  4, 0x0a, API_RESULT_INT32, false,
        {API_TYPE_UINT32, "UINT"}, GET_DLG_ITEM_TEXT_A_PARAMETERS},
    {"GetDlgItemTextW",  4, 0x0a, API_RESULT_INT32, false,
        {API_TYPE_UINT32, "UINT"}, GET_DLG_ITEM_TEXT_W_PARAMETERS},
    {"GetModuleHandleA", 1, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_POINTER, "HMODULE"}, GET_MODULE_HANDLE_A_PARAMETERS},
    {"GetModuleHandleW", 1, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_POINTER, "HMODULE"}, GET_MODULE_HANDLE_W_PARAMETERS},
    {"LoadIconA",        2, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_POINTER, "HICON"}, LOAD_ICON_A_PARAMETERS},
    {"LoadIconW",        2, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_POINTER, "HICON"}, LOAD_ICON_W_PARAMETERS},
    {"MessageBoxA",      4, 0x08, API_RESULT_INT32, false,
        {API_TYPE_INT32, "int"}, MESSAGE_BOX_A_PARAMETERS},
    {"MessageBoxW",      4, 0x08, API_RESULT_INT32, false,
        {API_TYPE_INT32, "int"}, MESSAGE_BOX_W_PARAMETERS},
    {"SendMessageA",     4, 0x02, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_INTPTR, "LRESULT"}, SEND_MESSAGE_PARAMETERS},
    {"SendMessageW",     4, 0x02, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_INTPTR, "LRESULT"}, SEND_MESSAGE_PARAMETERS},
    {"SetFocus",         1, 0x00, API_RESULT_POINTER_SIZED, false,
        {API_TYPE_POINTER, "HWND"}, SET_FOCUS_PARAMETERS},
    {"lstrlenA",         1, 0x00, API_RESULT_INT32, false,
        {API_TYPE_INT32, "int"}, LSTRLEN_A_PARAMETERS},
    {"lstrlenW",         1, 0x00, API_RESULT_INT32, false,
        {API_TYPE_INT32, "int"}, LSTRLEN_W_PARAMETERS}
};

bool hasDialogProcedureCallback(const KnownWin32Api &api) {
    return std::strcmp(api.name, "DialogBoxParamA") == 0 ||
           std::strcmp(api.name, "DialogBoxParamW") == 0;
}

QString canonicalImportName(QString name) {
    name = name.trimmed();

    if (name.size() >= 2 && name.startsWith(QLatin1Char('<')) && name.endsWith(QLatin1Char('>'))) {
        name = name.mid(1, name.size() - 2);
    }

    const int separator = std::max(
        std::max(name.lastIndexOf(QLatin1Char('!')), name.lastIndexOf(QLatin1Char(':'))),
        name.lastIndexOf(QLatin1Char('.')));
    if (separator >= 0) {
        name = name.mid(separator + 1);
    }

    if (name.startsWith(QLatin1String("JMP."), Qt::CaseInsensitive)) {
        name.remove(0, 4);
    }
    if (name.startsWith(QLatin1Char('&'))) {
        name.remove(0, 1);
    }
    if (name.startsWith(QLatin1String("__imp_"))) {
        name.remove(0, 6);
    }
    if (name.startsWith(QLatin1Char('_'))) {
        name.remove(0, 1);
    }

    const int suffix = name.lastIndexOf(QLatin1Char('@'));
    if (suffix >= 0) {
        bool isNumber = false;
        name.mid(suffix + 1).toULongLong(&isNumber);
        if (isNumber) {
            name.truncate(suffix);
        }
    }

    return name;
}

const KnownWin32Api *getKnownWin32Api(const QString &symbolName) {
    const QString name = canonicalImportName(symbolName);

    for (const auto &api : KNOWN_WIN32_APIS) {
        if (name == QLatin1String(api.name)) {
            return &api;
        }
    }

    return nullptr;
}

const core::image::Symbol *getImportSymbolAtSlot(const core::image::Image &image, ByteAddr slot) {
    const auto relocation = image.getRelocation(slot);
    if (relocation && relocation->symbol()->type() == core::image::SymbolType::FUNCTION) {
        return relocation->symbol();
    }
    return nullptr;
}

/* Resolve the standard six-byte FF /2 import call or FF /4 import jump form. */
const core::image::Symbol *getIndirectImport(const core::image::Image &image,
                                             ByteAddr instructionAddress,
                                             unsigned char modrm,
                                             SmallBitSize bitness) {
    unsigned char instruction[6];
    if (image.readBytes(instructionAddress, instruction, sizeof(instruction)) != sizeof(instruction) ||
        instruction[0] != 0xff || instruction[1] != modrm)
    {
        return nullptr;
    }

    std::uint32_t encodedAddress = 0;
    std::memcpy(&encodedAddress, instruction + 2, sizeof(encodedAddress));

    ByteAddr slot = encodedAddress;
    if (bitness == 64) {
        std::int32_t displacement = 0;
        std::memcpy(&displacement, instruction + 2, sizeof(displacement));

        const ByteSize instructionSize = sizeof(instruction);
        const ByteAddr maxAddress = (std::numeric_limits<ByteAddr>::max)();
        if (instructionAddress > maxAddress - instructionSize) {
            return nullptr;
        }
        const ByteAddr nextInstruction = instructionAddress + instructionSize;

        if (displacement < 0) {
            const ByteSize distance = -static_cast<ByteSize>(displacement);
            if (distance > nextInstruction) {
                return nullptr;
            }
            slot = nextInstruction - distance;
        } else {
            const ByteSize distance = displacement;
            if (nextInstruction > maxAddress - distance) {
                return nullptr;
            }
            slot = nextInstruction + distance;
        }
    }

    return getImportSymbolAtSlot(image, slot);
}

const core::image::Symbol *getImportedFunctionSymbol(const core::image::Image &image,
                                                     const core::ir::calling::CalleeId &calleeId,
                                                     SmallBitSize bitness) {
    if (calleeId.entryAddress()) {
        /* A direct call usually targets a six-byte "jmp [IAT]" linker thunk. */
        if (auto symbol = getIndirectImport(image, *calleeId.entryAddress(), 0x25, bitness)) {
            return symbol;
        }

        /* x64dbg can also provide a symbol for an already resolved target. */
        const auto symbol = image.getSymbol(*calleeId.entryAddress());
        if (symbol && symbol->type() == core::image::SymbolType::FUNCTION) {
            return symbol;
        }
    } else if (calleeId.callAddress()) {
        /* An unresolved "call [IAT]" is identified by its instruction address. */
        return getIndirectImport(image, *calleeId.callAddress(), 0x15, bitness);
    }

    return nullptr;
}

const core::image::Symbol *getImportedFunctionSymbol(const core::image::Image &image,
                                                     const core::ir::Call *call,
                                                     SmallBitSize bitness) {
    assert(call != nullptr);

    if (const auto target = call->target()->asConstant()) {
        const core::ir::calling::CalleeId calleeId(
            core::ir::calling::EntryAddress(target->value().value()));
        if (const auto symbol = getImportedFunctionSymbol(image, calleeId, bitness)) {
            return symbol;
        }
    }

    if (call->instruction()) {
        const core::ir::calling::CalleeId calleeId(
            core::ir::calling::CallAddress(call->instruction()->addr()));
        return getImportedFunctionSymbol(image, calleeId, bitness);
    }

    return nullptr;
}

bool setKnownWin32CallingConvention(core::Context &context,
                                    const core::ir::calling::CalleeId &calleeId,
                                    const QString &symbolName) {
    const auto api = getKnownWin32Api(symbolName);
    if (!api) {
        return false;
    }

    auto architecture = context.image()->platform().architecture();
    context.conventions()->setConvention(
        calleeId, architecture->getCallingConvention(QLatin1String("stdcall32")));
    context.conventions()->setStackArgumentsSize(
        calleeId, static_cast<ByteSize>(api->argumentCount) * 4);
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

bool isInt32Argument(const KnownWin32Api &api, std::size_t index) {
    return (api.int32ArgumentMask & (1U << index)) != 0;
}

std::shared_ptr<core::ir::Term> makeKnownArgument(const KnownWin32Api &api,
                                                  std::size_t index,
                                                  SmallBitSize bitness) {
    assert(index < api.argumentCount);
    assert(bitness == 32 || bitness == 64);

    if (bitness == 64 && index < 4) {
        const core::arch::Register *pointerRegisters[] = {
            X86Registers::rcx(), X86Registers::rdx(), X86Registers::r8(), X86Registers::r9()
        };
        const core::arch::Register *int32Registers[] = {
            X86Registers::ecx(), X86Registers::edx(), X86Registers::r8d(), X86Registers::r9d()
        };
        const auto reg = isInt32Argument(api, index) ? int32Registers[index] : pointerRegisters[index];
        return std::make_shared<core::ir::MemoryLocationAccess>(reg->memoryLocation());
    }

    const auto stackPointer = bitness == 64 ? X86Registers::rsp() : X86Registers::esp();
    const ByteSize slotSize = bitness / CHAR_BIT;
    const ByteSize offset = bitness == 64 ?
        5 * slotSize + static_cast<ByteSize>(index - 4) * slotSize :
        static_cast<ByteSize>(index + 1) * slotSize;
    const SmallBitSize valueSize = bitness == 64 && isInt32Argument(api, index) ? 32 : bitness;

    return std::make_shared<core::ir::Dereference>(
        std::make_unique<core::ir::BinaryOperator>(
            core::ir::BinaryOperator::ADD,
            std::make_unique<core::ir::MemoryLocationAccess>(stackPointer->memoryLocation()),
            std::make_unique<core::ir::Constant>(SizedValue(bitness, offset)),
            bitness),
        core::ir::MemoryDomain::MEMORY,
        valueSize);
}

core::ir::calling::TypeDescription makeTypeDescription(const KnownApiType &type,
                                                        SmallBitSize bitness) {
    using core::ir::calling::TypeDescription;

    const QString displayName = QLatin1String(type.name);
    switch (type.kind) {
        case API_TYPE_VOID:
            return TypeDescription(TypeDescription::VOID, 0, false, displayName);
        case API_TYPE_INT32:
            return TypeDescription(TypeDescription::INTEGER, 32, false, displayName);
        case API_TYPE_UINT32:
            return TypeDescription(TypeDescription::INTEGER, 32, true, displayName);
        case API_TYPE_INTPTR:
            return TypeDescription(TypeDescription::INTEGER, bitness, false, displayName);
        case API_TYPE_UINTPTR:
            return TypeDescription(TypeDescription::INTEGER, bitness, true, displayName);
        case API_TYPE_POINTER:
            return TypeDescription(TypeDescription::POINTER, bitness, true, displayName);
    }

    unreachable();
    return TypeDescription(TypeDescription::VOID, 0, false);
}

std::shared_ptr<const core::ir::calling::FunctionPrototype> makeFunctionPrototype(
        const KnownApiType &returnType,
        const KnownApiParameter *parameters,
        std::size_t parameterCount,
        SmallBitSize bitness,
        const QString &preferredName = QString()) {
    std::vector<core::ir::calling::ParameterDescription> parameterDescriptions;
    parameterDescriptions.reserve(parameterCount);

    for (std::size_t index = 0; index < parameterCount; ++index) {
        parameterDescriptions.emplace_back(
            QLatin1String(parameters[index].name),
            makeTypeDescription(parameters[index].type, bitness),
            parameters[index].mayWriteMemory);
    }

    return std::make_shared<core::ir::calling::FunctionPrototype>(
        makeTypeDescription(returnType, bitness),
        std::move(parameterDescriptions),
        bitness == 32 ? QLatin1String("__stdcall") : QString(),
        preferredName);
}

std::shared_ptr<core::ir::calling::FunctionSignature> makeKnownFunctionSignature(const KnownWin32Api &api,
                                                                                 SmallBitSize bitness) {
    auto signature = std::make_shared<core::ir::calling::FunctionSignature>();

    signature->setPrototype(makeFunctionPrototype(
        api.returnType, api.parameters, api.argumentCount, bitness));

    for (std::size_t index = 0; index < api.argumentCount; ++index) {
        signature->arguments().push_back(makeKnownArgument(api, index, bitness));
    }

    if (api.resultKind != API_RESULT_VOID) {
        const auto resultRegister = bitness == 32 || api.resultKind == API_RESULT_INT32 ?
            X86Registers::eax() : X86Registers::rax();
        signature->setReturnValue(
            std::make_shared<core::ir::MemoryLocationAccess>(resultRegister->memoryLocation()));
    }

    return signature;
}

std::shared_ptr<core::ir::calling::FunctionSignature> makeDialogProcedureSignature(
        const QString &preferredName) {
    auto signature = std::make_shared<core::ir::calling::FunctionSignature>();

    signature->setPrototype(makeFunctionPrototype(
        KnownApiType{API_TYPE_INTPTR, "INT_PTR"},
        DIALOG_PROCEDURE_PARAMETERS,
        sizeof(DIALOG_PROCEDURE_PARAMETERS) / sizeof(DIALOG_PROCEDURE_PARAMETERS[0]),
        32,
        preferredName));

    for (std::size_t index = 0; index < 4; ++index) {
        signature->arguments().push_back(
            std::make_shared<core::ir::Dereference>(
                std::make_unique<core::ir::BinaryOperator>(
                    core::ir::BinaryOperator::ADD,
                    std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::esp()->memoryLocation()),
                    std::make_unique<core::ir::Constant>(SizedValue(32, (index + 1) * 4)),
                    32),
                core::ir::MemoryDomain::MEMORY,
                32));
    }

    signature->setReturnValue(
        std::make_shared<core::ir::MemoryLocationAccess>(X86Registers::eax()->memoryLocation()));
    return signature;
}

boost::optional<ByteAddr> getConcreteStackArgument(const core::ir::Call *call,
                                                   const core::ir::dflow::Dataflow &dataflow,
                                                   const core::ir::calling::Hooks &hooks,
                                                   std::size_t index) {
    const auto callHook = hooks.getCallHook(call);
    if (!callHook || !callHook->stackPointer() || !callHook->snapshotStatement()) {
        return boost::none;
    }

    const auto stackPointerValue = dataflow.getValue(callHook->stackPointer());
    if (!stackPointerValue->isStackOffset()) {
        return boost::none;
    }

    const BitAddr argumentAddress =
        (stackPointerValue->stackOffset() + static_cast<SignedConstantValue>((index + 1) * 4)) * CHAR_BIT;
    const core::ir::MemoryLocation argumentLocation(
        core::ir::MemoryDomain::STACK, argumentAddress, 32);
    const auto definitions = dataflow.getDefinitions(callHook->snapshotStatement()).projected(argumentLocation);

    if (definitions.chunks().size() != 1 ||
        definitions.chunks().front().location() != argumentLocation ||
        definitions.chunks().front().hasUnknownDefinition() ||
        definitions.chunks().front().definitions().empty())
    {
        return boost::none;
    }

    boost::optional<ConstantValue> result;
    foreach (const auto definition, definitions.chunks().front().definitions()) {
        const auto value = dataflow.getValue(definition);
        if (!value->abstractValue().isConcrete()) {
            return boost::none;
        }

        const ConstantValue concrete = value->abstractValue().asConcrete().value();
        if (result && *result != concrete) {
            return boost::none;
        }
        result = concrete;
    }

    if (!result) {
        return boost::none;
    }
    return static_cast<ByteAddr>(*result);
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

bool canUseDialogProcedureName(const core::Context &context,
                               ByteAddr address,
                               std::size_t procedureCount) {
    const auto addressSymbol = context.image()->getSymbol(address);
    if (procedureCount != 1 ||
        (addressSymbol && !addressSymbol->name().trimmed().isEmpty())) {
        return false;
    }

    foreach (const auto symbol, context.image()->symbols()) {
        if (canonicalImportName(symbol->name()).compare(
                QLatin1String("DialogFunc"), Qt::CaseInsensitive) == 0)
        {
            return false;
        }
    }

    return true;
}

void setKnownFunctionSignature(core::Context &context,
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

void setKnownCallSignature(core::Context &context,
                           const core::ir::calling::CalleeId &calleeId,
                           const std::shared_ptr<core::ir::calling::FunctionSignature> &functionSignature,
                           const core::ir::Call *call) {
    auto callSignature = std::make_shared<core::ir::calling::CallSignature>();

    callSignature->arguments() = functionSignature->arguments();
    callSignature->setReturnValue(functionSignature->returnValue());
    callSignature->setPrototype(functionSignature->prototype());
    context.signatures()->setSignature(call, callSignature);

    if (calleeId.entryAddress()) {
        context.signatures()->setSignature(*calleeId.entryAddress(), functionSignature);
    }
}

void applyKnownWin32Signatures(core::Context &context) {
    const auto bitness = context.image()->platform().architecture()->bitness();
    const auto &dataflows = *context.dataflows();
    std::map<const KnownWin32Api *, std::shared_ptr<core::ir::calling::FunctionSignature>> signatures;
    std::set<ByteAddr> dialogProcedures;

    auto getSignature = [&](const KnownWin32Api *api) {
        auto &signature = signatures[api];
        if (!signature) {
            signature = makeKnownFunctionSignature(*api, bitness);
        }
        return signature;
    };

    for (const auto &functionAndDataflow : dataflows) {
        const auto function = functionAndDataflow.first;
        const auto &dataflow = *functionAndDataflow.second;
        const auto functionId = core::ir::calling::getCalleeId(function);

        if (const auto symbol = getImportedFunctionSymbol(*context.image(), functionId, bitness)) {
            if (const auto api = getKnownWin32Api(symbol->name())) {
                setKnownFunctionSignature(context, functionId, getSignature(api), function);
            }
        }

        foreach (const auto basicBlock, function->basicBlocks()) {
            foreach (const auto statement, basicBlock->statements()) {
                const auto call = statement->asCall();
                if (!call) {
                    continue;
                }

                const auto calleeId = core::ir::calling::getCalleeId(call, dataflow);
                auto symbol = getImportedFunctionSymbol(*context.image(), calleeId, bitness);
                if (!symbol) {
                    /* Keep the IAT relocation usable even if dataflow resolved its pointee. */
                    symbol = getImportedFunctionSymbol(*context.image(), call, bitness);
                }
                if (!symbol) {
                    continue;
                }

                if (const auto api = getKnownWin32Api(symbol->name())) {
                    if (bitness == 32 && hasDialogProcedureCallback(*api)) {
                        if (const auto address = getConcreteStackArgument(
                                call, dataflow, *context.hooks(), 3))
                        {
                            dialogProcedures.insert(*address);
                        }
                    }
                    setKnownCallSignature(context, calleeId, getSignature(api), call);
                }
            }
        }
    }

    if (bitness == 32) {
        const auto stdcall32 = context.image()->platform().architecture()->getCallingConvention(
            QLatin1String("stdcall32"));

        foreach (const ByteAddr address, dialogProcedures) {
            auto function = getFunctionAtAddress(context, address);
            if (!function) {
                continue;
            }

            const core::ir::calling::CalleeId calleeId{
                core::ir::calling::EntryAddress(address)};
            context.conventions()->setConvention(calleeId, stdcall32);
            context.conventions()->setStackArgumentsSize(calleeId, static_cast<ByteSize>(16));
            setKnownFunctionSignature(
                context,
                calleeId,
                makeDialogProcedureSignature(
                    canUseDialogProcedureName(context, address, dialogProcedures.size()) ?
                        QLatin1String("DialogFunc") : QString()),
                function);
        }
    }
}

void terminateKnownNoReturnCalls(core::Context &context) {
    auto program = const_cast<core::ir::Program *>(context.program());
    const auto bitness = context.image()->platform().architecture()->bitness();
    std::vector<core::ir::Call *> noReturnCalls;

    foreach (const auto basicBlock, program->basicBlocks()) {
        foreach (const auto statement, basicBlock->statements()) {
            const auto call = statement->as<core::ir::Call>();
            if (!call) {
                continue;
            }

            const auto symbol = getImportedFunctionSymbol(*context.image(), call, bitness);
            const auto api = symbol ? getKnownWin32Api(symbol->name()) : nullptr;
            if (api && api->doesNotReturn) {
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
        terminateKnownNoReturnCalls(context);
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

    if (architecture->bitness() == 32) {
        using core::ir::calling::CalleeId;
        using core::ir::calling::EntryAddress;

        auto stdcall32 = architecture->getCallingConvention(QLatin1String("stdcall32"));
        const bool isWindows = context.image()->platform().operatingSystem() == core::image::Platform::Windows;

        foreach (auto symbol, context.image()->symbols()) {
            if (!symbol->value()) {
                continue;
            }
            CalleeId calleeId(EntryAddress(*symbol->value()));
            if (isWindows && setKnownWin32CallingConvention(context, calleeId, symbol->name())) {
                continue;
            }
            if (isWindows && symbol->type() == core::image::SymbolType::FUNCTION &&
                setExplicitThiscallConvention(context, calleeId, symbol->name()))
            {
                continue;
            }
            auto index = symbol->name().lastIndexOf(QChar('@'));
            if (index == -1) {
                continue;
            }
            auto argumentsSize = stringToInt<ByteSize>(symbol->name().mid(index + 1));
            if (!argumentsSize) {
                continue;
            }
            context.conventions()->setConvention(calleeId, stdcall32);
            context.conventions()->setStackArgumentsSize(calleeId, *argumentsSize);
        }

        ud_t ud_obj_;
        ud_init(&ud_obj_);
        ud_set_mode(&ud_obj_, context.image()->platform().architecture()->bitness());

        foreach (auto function, context.functions()->list()) {
            if (!function->entry()->address()) {
                continue;
            }
            foreach (auto basicBlock, function->basicBlocks()) {
                auto terminator = basicBlock->getTerminator();
                if (!terminator) {
                    continue;
                }
                auto instruction = checked_cast<const X86Instruction *>(terminator->instruction());
                if (!instruction) {
                    continue;
                }

                ud_set_pc(&ud_obj_, instruction->addr());
                ud_set_input_buffer(&ud_obj_, const_cast<uint8_t *>(instruction->bytes()),
                                    checked_cast<std::size_t>(instruction->size()));
                ud_disassemble(&ud_obj_);

                assert(ud_obj_.mnemonic != UD_Iinvalid);

                if (ud_obj_.mnemonic != UD_Iret) {
                    continue;
                }

                if (ud_obj_.operand[0].type == UD_NONE) {
                    continue;
                }
                assert(ud_obj_.operand[0].type == UD_OP_IMM && ud_obj_.operand[0].size == 16);

                CalleeId calleeId(EntryAddress(*function->entry()->address()));
                /* Preserve a stronger symbol-derived result such as __thiscall. */
                if (!context.conventions()->getConvention(calleeId)) {
                    context.conventions()->setConvention(calleeId, stdcall32);
                }
                context.conventions()->setStackArgumentsSize(calleeId, ud_obj_.operand[0].lval.uword);
            }
        }
    }
}

void X86MasterAnalyzer::detectCallingConvention(core::Context &context, const core::ir::calling::CalleeId &calleeId) const {
    const auto &platform = context.image()->platform();
    auto architecture = platform.architecture();

    if (architecture->bitness() == 32 && platform.operatingSystem() == core::image::Platform::Windows) {
        if (auto symbol = getImportedFunctionSymbol(*context.image(), calleeId, architecture->bitness())) {
            if (setKnownWin32CallingConvention(context, calleeId, symbol->name())) {
                return;
            }
            if (setExplicitThiscallConvention(context, calleeId, symbol->name())) {
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
        applyKnownWin32Signatures(context);
    }
}

} // namespace x86
} // namespace arch
} // namespace nc

/* vim:set et sts=4 sw=4: */
