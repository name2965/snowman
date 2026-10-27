/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "CallingConventions.h"

#include <initializer_list>

#include <nc/common/make_unique.h>

#include <nc/core/arch/Register.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>

#include "X86Architecture.h"
#include "X86Registers.h"

namespace nc {
namespace arch {
namespace x86 {

namespace {

typedef core::arch::Register Register;
typedef core::ir::MemoryLocation MemoryLocation;

void appendLocations(std::vector<MemoryLocation> &result,
                     std::initializer_list<const Register *> registers) {
    for (const Register *reg : registers) {
        assert(reg != nullptr);
        result.push_back(reg->memoryLocation());
    }
}

std::vector<MemoryLocation> volatileCallState(
        std::initializer_list<const Register *> generalPurpose,
        std::size_t xmmCount) {
    std::vector<MemoryLocation> result;
    appendLocations(result, generalPurpose);

    /* Arithmetic flags are caller state. DF is deliberately excluded: all
     * supported x86 ABIs require it to be clear across calls. */
    appendLocations(result, {
        X86Registers::cf(), X86Registers::pf(), X86Registers::af(),
        X86Registers::zf(), X86Registers::sf(), X86Registers::of(),
        X86Registers::less(), X86Registers::less_or_equal(),
        X86Registers::below_or_equal(), X86Registers::fpu_status_word()
    });

    const Register *const floatingStack[] = {
        X86Registers::st0(), X86Registers::st1(), X86Registers::st2(),
        X86Registers::st3(), X86Registers::st4(), X86Registers::st5(),
        X86Registers::st6(), X86Registers::st7()
    };
    const Register *const multimedia[] = {
        X86Registers::mm0(), X86Registers::mm1(), X86Registers::mm2(),
        X86Registers::mm3(), X86Registers::mm4(), X86Registers::mm5(),
        X86Registers::mm6(), X86Registers::mm7()
    };
    const Register *const vectors[] = {
        X86Registers::xmm0(), X86Registers::xmm1(), X86Registers::xmm2(),
        X86Registers::xmm3(), X86Registers::xmm4(), X86Registers::xmm5(),
        X86Registers::xmm6(), X86Registers::xmm7(), X86Registers::xmm8(),
        X86Registers::xmm9(), X86Registers::xmm10(), X86Registers::xmm11(),
        X86Registers::xmm12(), X86Registers::xmm13(), X86Registers::xmm14(),
        X86Registers::xmm15()
    };
    for (const Register *reg : floatingStack) {
        result.push_back(reg->memoryLocation());
    }
    for (const Register *reg : multimedia) {
        result.push_back(reg->memoryLocation());
    }
    const std::size_t availableVectors =
        sizeof(vectors) / sizeof(vectors[0]);
    assert(xmmCount <= availableVectors);
    for (std::size_t index = 0; index < xmmCount; ++index) {
        result.push_back(vectors[index]->memoryLocation());
    }
    return result;
}

} // anonymous namespace

AMD64CallingConvention::AMD64CallingConvention(const X86Architecture *architecture):
    Convention(QLatin1String("amd64"))
{
    setStackPointer(architecture->stackPointer()->memoryLocation());

    setFirstArgumentOffset(architecture->bitness());
    setArgumentAlignment(architecture->bitness());

    /* Used for integer and pointer arguments. */
    std::vector<core::ir::MemoryLocation> scalarArgs;
    scalarArgs.push_back(X86Registers::rdi()->memoryLocation());
    scalarArgs.push_back(X86Registers::rsi()->memoryLocation());
    scalarArgs.push_back(X86Registers::rdx()->memoryLocation());
    scalarArgs.push_back(X86Registers::rcx()->memoryLocation());
    scalarArgs.push_back(X86Registers::r8()->memoryLocation());
    scalarArgs.push_back(X86Registers::r9()->memoryLocation());
    addArgumentGroup(std::move(scalarArgs));

    /* Used for floating-point arguments. */
    std::vector<core::ir::MemoryLocation> fpArgs;
    fpArgs.push_back(X86Registers::xmm0()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm1()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm2()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm3()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm4()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm5()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm6()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm7()->memoryLocation());
    addArgumentGroup(std::move(fpArgs));

    addReturnValueLocation(X86Registers::rax()->memoryLocation());
    addReturnValueLocation(X86Registers::xmm0()->memoryLocation());
    addClobberedLocations(volatileCallState({
        X86Registers::rax(), X86Registers::rcx(), X86Registers::rdx(),
        X86Registers::rsi(), X86Registers::rdi(), X86Registers::r8(),
        X86Registers::r9(), X86Registers::r10(), X86Registers::r11()
    }, 16));

    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(core::ir::MemoryLocation(core::ir::MemoryDomain::STACK, 0, architecture->bitness())),
        std::make_unique<core::ir::Intrinsic>(core::ir::Intrinsic::RETURN_ADDRESS, architecture->bitness()),
        core::ir::Assignment::CONTROL_FLOW_STATE
    ));
    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::df()->memoryLocation()),
        std::make_unique<core::ir::Constant>(SizedValue(X86Registers::df()->size(), 0))
    ));
}

Microsoft64CallingConvention::Microsoft64CallingConvention(const X86Architecture *architecture):
    Convention(QLatin1String("microsoft64"))
{
    setStackPointer(architecture->stackPointer()->memoryLocation());

    /* Skip the return address and the four-register home space. */
    setFirstArgumentOffset(architecture->bitness() * 5);
    setArgumentAlignment(architecture->bitness());

    /* Used for integer and pointer arguments. */
    std::vector<core::ir::MemoryLocation> scalarArgs;
    scalarArgs.push_back(X86Registers::rcx()->memoryLocation());
    scalarArgs.push_back(X86Registers::rdx()->memoryLocation());
    scalarArgs.push_back(X86Registers::r8()->memoryLocation());
    scalarArgs.push_back(X86Registers::r9()->memoryLocation());
    addArgumentGroup(std::move(scalarArgs));

    /* Used for floating-point arguments. */
    std::vector<core::ir::MemoryLocation> fpArgs;
    fpArgs.push_back(X86Registers::xmm0()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm1()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm2()->memoryLocation());
    fpArgs.push_back(X86Registers::xmm3()->memoryLocation());
    addArgumentGroup(std::move(fpArgs));

    addReturnValueLocation(X86Registers::rax()->memoryLocation());
    addReturnValueLocation(X86Registers::xmm0()->memoryLocation());
    addClobberedLocations(volatileCallState({
        X86Registers::rax(), X86Registers::rcx(), X86Registers::rdx(),
        X86Registers::r8(), X86Registers::r9(), X86Registers::r10(),
        X86Registers::r11()
    }, 6));

    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(core::ir::MemoryLocation(core::ir::MemoryDomain::STACK, 0, architecture->bitness())),
        std::make_unique<core::ir::Intrinsic>(core::ir::Intrinsic::RETURN_ADDRESS, architecture->bitness()),
        core::ir::Assignment::CONTROL_FLOW_STATE
    ));
    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::df()->memoryLocation()),
        std::make_unique<core::ir::Constant>(SizedValue(X86Registers::df()->size(), 0))
    ));
}

Cdecl32CallingConvention::Cdecl32CallingConvention(const X86Architecture *architecture):
    Convention(QLatin1String("cdecl32"))
{
    setStackPointer(architecture->stackPointer()->memoryLocation());

    setFirstArgumentOffset(architecture->bitness());
    setArgumentAlignment(architecture->bitness());

    addReturnValueLocation(X86Registers::eax()->memoryLocation());
    addReturnValueLocation(X86Registers::st0()->memoryLocation());
    addClobberedLocations(volatileCallState({
        X86Registers::eax(), X86Registers::ecx(), X86Registers::edx()
    }, 8));

    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(core::ir::MemoryLocation(core::ir::MemoryDomain::STACK, 0, architecture->bitness())),
        std::make_unique<core::ir::Intrinsic>(core::ir::Intrinsic::RETURN_ADDRESS, architecture->bitness()),
        core::ir::Assignment::CONTROL_FLOW_STATE
    ));
    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::df()->memoryLocation()),
        std::make_unique<core::ir::Constant>(SizedValue(X86Registers::df()->size(), 0))
    ));
}

Cdecl16CallingConvention::Cdecl16CallingConvention(const X86Architecture *architecture):
    Convention(QLatin1String("cdecl16"))
{
    setStackPointer(architecture->stackPointer()->memoryLocation());

    setFirstArgumentOffset(architecture->bitness());
    setArgumentAlignment(architecture->bitness());

    addReturnValueLocation(X86Registers::ax()->memoryLocation());
    addReturnValueLocation(X86Registers::st0()->memoryLocation());
    addClobberedLocations(volatileCallState({
        X86Registers::ax(), X86Registers::cx(), X86Registers::dx()
    }, 0));

    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(core::ir::MemoryLocation(core::ir::MemoryDomain::STACK, 0, architecture->bitness())),
        std::make_unique<core::ir::Intrinsic>(core::ir::Intrinsic::RETURN_ADDRESS, architecture->bitness()),
        core::ir::Assignment::CONTROL_FLOW_STATE
    ));
    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::df()->memoryLocation()),
        std::make_unique<core::ir::Constant>(SizedValue(X86Registers::df()->size(), 0))
    ));
}

Stdcall32CallingConvention::Stdcall32CallingConvention(const X86Architecture *architecture):
    Convention(QLatin1String("stdcall32"))
{
    setStackPointer(architecture->stackPointer()->memoryLocation());

    setFirstArgumentOffset(architecture->bitness());
    setArgumentAlignment(architecture->bitness());
    setCalleeCleanup(true);

    addReturnValueLocation(X86Registers::eax()->memoryLocation());
    addReturnValueLocation(X86Registers::st0()->memoryLocation());
    addClobberedLocations(volatileCallState({
        X86Registers::eax(), X86Registers::ecx(), X86Registers::edx()
    }, 8));

    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(core::ir::MemoryLocation(core::ir::MemoryDomain::STACK, 0, architecture->bitness())),
        std::make_unique<core::ir::Intrinsic>(core::ir::Intrinsic::RETURN_ADDRESS, architecture->bitness()),
        core::ir::Assignment::CONTROL_FLOW_STATE
    ));
    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::df()->memoryLocation()),
        std::make_unique<core::ir::Constant>(SizedValue(X86Registers::df()->size(), 0))
    ));
}

Thiscall32CallingConvention::Thiscall32CallingConvention(const X86Architecture *architecture):
    Convention(QLatin1String("thiscall32"))
{
    setStackPointer(architecture->stackPointer()->memoryLocation());

    setFirstArgumentOffset(architecture->bitness());
    setArgumentAlignment(architecture->bitness());
    setCalleeCleanup(true);

    addArgumentGroup(std::vector<core::ir::MemoryLocation>(1, X86Registers::ecx()->memoryLocation()));
    /* Stack arguments remain recoverable even when an unused 'this' is not read. */
    addArgumentGroup(std::vector<core::ir::MemoryLocation>());

    addReturnValueLocation(X86Registers::eax()->memoryLocation());
    addReturnValueLocation(X86Registers::st0()->memoryLocation());
    addClobberedLocations(volatileCallState({
        X86Registers::eax(), X86Registers::ecx(), X86Registers::edx()
    }, 8));

    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(core::ir::MemoryLocation(core::ir::MemoryDomain::STACK, 0, architecture->bitness())),
        std::make_unique<core::ir::Intrinsic>(core::ir::Intrinsic::RETURN_ADDRESS, architecture->bitness()),
        core::ir::Assignment::CONTROL_FLOW_STATE
    ));
    addEnterStatement(std::make_unique<core::ir::Assignment>(
        std::make_unique<core::ir::MemoryLocationAccess>(X86Registers::df()->memoryLocation()),
        std::make_unique<core::ir::Constant>(SizedValue(X86Registers::df()->size(), 0))
    ));
}

} // namespace x86
} // namespace arch
} // namespace nc

/* vim:set et ts=4 sw=4: */
