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

#include "X86Instruction.h"

#include <limits>

#include <QTextStream>

#include "udis86.h"

namespace nc {
namespace arch {
namespace x86 {

namespace {

SignedConstantValue getSignedDisplacement(const ud_operand &operand) {
    switch (operand.offset) {
        case 0:  return 0;
        case 8:  return operand.lval.sbyte;
        case 16: return operand.lval.sword;
        case 32: return operand.lval.sdword;
        case 64: return operand.lval.sqword;
        default: return 0;
    }
}

ConstantValue getUnsignedDisplacement(const ud_operand &operand) {
    switch (operand.offset) {
        case 0:  return 0;
        case 8:  return operand.lval.ubyte;
        case 16: return operand.lval.uword;
        case 32: return operand.lval.udword;
        case 64: return operand.lval.uqword;
        default: return 0;
    }
}

bool hasSupportedDisplacementSize(const ud_operand &operand) {
    return operand.offset == 0 || operand.offset == 8 ||
           operand.offset == 16 || operand.offset == 32 ||
           operand.offset == 64;
}

} // anonymous namespace

bool X86Instruction::getStaticMemoryControlTransferAddress(
        ControlTransferKind kind, ByteAddr &address) const {
    if (addr() < 0) {
        return false;
    }

    ud_t ud_obj;
    ud_init(&ud_obj);
    ud_set_mode(&ud_obj, bitness_);
    ud_set_pc(&ud_obj, addr());
    ud_set_input_buffer(&ud_obj, const_cast<uint8_t *>(bytes()), size());

    const unsigned int decodedSize = ud_disassemble(&ud_obj);
    if (decodedSize != static_cast<unsigned int>(size()) ||
        ud_obj.mnemonic == UD_Iinvalid)
    {
        return false;
    }

    const enum ud_mnemonic_code expectedMnemonic =
        kind == ControlTransferKind::CALL ? UD_Icall : UD_Ijmp;
    const ud_operand &operand = ud_obj.operand[0];
    if (ud_obj.mnemonic != expectedMnemonic || !ud_obj.br_near ||
        operand.type != UD_OP_MEM || ud_obj.operand[1].type != UD_NONE ||
        operand.index != UD_NONE || !hasSupportedDisplacementSize(operand))
    {
        return false;
    }

    /* Segment-relative pointers are process/thread state, not image VAs. */
    if (ud_obj.pfx_seg != 0 && ud_obj.pfx_seg != UD_R_DS) {
        return false;
    }

    const ByteAddr maxAddress = (std::numeric_limits<ByteAddr>::max)();
    if (operand.base == UD_R_RIP) {
        if (bitness_ != 64 || addr() < 0 || size() < 0 ||
            addr() > maxAddress - size())
        {
            return false;
        }

        const ByteAddr nextInstruction = addr() + size();
        const SignedConstantValue displacement = getSignedDisplacement(operand);
        if (displacement < 0) {
            if (displacement ==
                (std::numeric_limits<SignedConstantValue>::min)())
            {
                return false;
            }
            const ByteSize distance = -displacement;
            if (distance > nextInstruction) {
                return false;
            }
            address = nextInstruction - distance;
        } else {
            const ByteSize distance = displacement;
            if (distance > maxAddress - nextInstruction) {
                return false;
            }
            address = nextInstruction + distance;
        }
        return true;
    }

    /*
     * A base-less 16/32-bit address is an unsigned absolute address.  Do not
     * guess the sign-extension rules of a base-less 64-bit addressing form;
     * normal x86-64 image references are represented as RIP-relative above.
     */
    if (operand.base != UD_NONE ||
        (ud_obj.adr_mode != 16 && ud_obj.adr_mode != 32))
    {
        return false;
    }

    const ConstantValue absoluteAddress = getUnsignedDisplacement(operand);
    if (absoluteAddress > static_cast<ConstantValue>(maxAddress)) {
        return false;
    }
    address = static_cast<ByteAddr>(absoluteAddress);
    return true;
}

void X86Instruction::print(QTextStream &out) const {
    ud_t ud_obj;

    ud_init(&ud_obj);
    ud_set_mode(&ud_obj, bitness_);
    ud_set_syntax(&ud_obj, UD_SYN_INTEL);
    ud_set_pc(&ud_obj, addr());
    ud_set_input_buffer(&ud_obj, const_cast<uint8_t *>(bytes()), size());
    ud_disassemble(&ud_obj);

    assert(ud_obj.mnemonic != UD_Iinvalid);

    out << ud_insn_asm(&ud_obj);
}

} // namespace x86
} // namespace arch
} // namespace nc

/* vim:set et sts=4 sw=4: */
