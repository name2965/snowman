/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "Disassembler.h"

#include <algorithm> /* std::max() */

#include <nc/core/image/ByteSource.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Relocation.h>

#include <nc/common/CancellationToken.h>

#include "Architecture.h"
#include "Instruction.h"

namespace nc {
namespace core {
namespace arch {

void Disassembler::disassemble(const image::Image *image, const image::ByteSource *source, ByteAddr begin, ByteAddr end, InstructionCallback callback, const CancellationToken &canceled) {
    assert(source != nullptr);
    assert(begin <= end);

    /* Native byte addresses are nonnegative.  Keeping this invariant also
     * makes every distance below representable in the signed ByteSize type. */
    if (!source || begin < 0 || begin >= end) {
        return;
    }

    const SmallByteSize maxInstructionSize = architecture_->maxInstructionSize();
    const ByteSize bufferSize = std::min(ByteSize(std::max(65536, maxInstructionSize)), end - begin);
    const std::unique_ptr<char[]> buffer(new char[bufferSize]);

    auto bufferBegin = begin;
    auto bufferEnd = begin;

    for (ByteAddr pc = begin; pc < end; canceled.poll()) {
        const bool bufferNeedsRefill = bufferEnd < pc ||
            static_cast<ByteSize>(maxInstructionSize) > bufferEnd - pc;
        if (bufferNeedsRefill && bufferEnd < end) {
            bufferBegin = pc;
            const ByteSize requested = std::min(bufferSize, end - pc);
            const ByteSize bytesRead = source->readBytes(
                pc, buffer.get(), requested);
            /* Do not trust a ByteSource implementation enough to perform
             * arithmetic with an out-of-contract result. */
            bufferEnd = bytesRead >= 0 && bytesRead <= requested ?
                bufferBegin + bytesRead : bufferBegin;
        }

        const image::Relocation* reloc = image->getRelocation(pc);
        // If a relocation starts at a particular address it does make sense for there to be an instruction
        // there as well so skip over it
        if (reloc) {
            const ByteSize relocationSize = reloc->size();
            if (relocationSize <= 0) {
                ++pc;
            } else if (relocationSize >= end - pc) {
                pc = end;
            } else {
                pc += relocationSize;
            }
            continue;
        }

        auto instruction = disassembleSingleInstruction(pc, buffer.get() + (pc - bufferBegin), bufferEnd - pc);

        if (instruction && instruction->size() > 0 &&
            static_cast<ByteSize>(instruction->size()) <= bufferEnd - pc)
        {
            /* Advancing inside the checked buffer range avoids relying on
             * Instruction::endAddr() when pc is near ByteAddr's maximum. */
            pc += instruction->size();
            callback(std::move(instruction));
        } else {
            ++pc;
        }
    }
}

std::shared_ptr<Instruction> Disassembler::disassembleSingleInstruction(ByteAddr pc, const image::ByteSource *source) {
    const SmallByteSize maxInstructionSize = architecture_->maxInstructionSize();
    const std::unique_ptr<char[]> buffer(new char[maxInstructionSize]);

    return disassembleSingleInstruction(
        pc,
        buffer.get(),
        source->readBytes(pc, buffer.get(), maxInstructionSize));
}

} // namespace arch
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
