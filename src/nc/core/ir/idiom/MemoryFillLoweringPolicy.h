/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace ir {
namespace idiom {

/**
 * Architecture-neutral facts required to replace a proved memory-fill loop
 * with a call to a byte-oriented library primitive.
 *
 * Recognition and lowering deliberately remain separate: a loop may have a
 * valid MemoryFill descriptor while retaining its loop form because object
 * bounds, pointer arithmetic, or target memory semantics are not proved.
 */
struct MemoryFillLoweringFacts {
    bool dataflowConverged;
    SmallBitSize pointerSize;
    SmallBitSize addressSize;
    SmallBitSize destinationSize;
    SmallBitSize elementSize;
    SignedConstantValue stride;

    /*
     * A non-constant fill value may have been captured before loop entry.
     * Re-emitting its source expression at the loop's structured location
     * can observe a later state, so lowering requires the captured value to
     * be representable independently of that source expression.
     */
    bool fillIsConcrete;
    ConstantValue fill;

    bool countIsConcrete;
    ConstantValue count;

    bool destinationIsConcrete;
    bool destinationMayBeStackOffset;
    ConstantValue destination;

    bool hasContainingSection;
    ByteAddr sectionAddress;
    ByteSize sectionSize;
    bool sectionIsAllocated;
    bool sectionIsWritable;
    bool sectionIsExecutable;

    MemoryFillLoweringFacts();
};

/**
 * Returns true only when replacing the loop with memset preserves the proved
 * byte writes without introducing a zero-trip evaluation, pointer wrap, a
 * cross-object access, or target-dependent wide-store behavior.
 */
bool isMemoryFillLoweringSafe(const MemoryFillLoweringFacts &facts);

} // namespace idiom
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
