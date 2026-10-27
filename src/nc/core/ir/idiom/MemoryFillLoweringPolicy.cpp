/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "MemoryFillLoweringPolicy.h"

#include <climits>
#include <limits>

#include <nc/common/BitTwiddling.h>

namespace nc {
namespace core {
namespace ir {
namespace idiom {

MemoryFillLoweringFacts::MemoryFillLoweringFacts():
    dataflowConverged(false), pointerSize(0), addressSize(0),
    destinationSize(0), elementSize(0), stride(0),
    fillIsConcrete(false), fill(0), countIsConcrete(false), count(0),
    destinationIsConcrete(false),
    destinationMayBeStackOffset(true), destination(0),
    hasContainingSection(false), sectionAddress(0), sectionSize(0),
    sectionIsAllocated(false), sectionIsWritable(false),
    sectionIsExecutable(false)
{}

bool isMemoryFillLoweringSafe(const MemoryFillLoweringFacts &facts) {
    if (!facts.dataflowConverged || facts.pointerSize <= 0 ||
        facts.pointerSize > static_cast<SmallBitSize>(
            sizeof(ConstantValue) * CHAR_BIT) ||
        facts.addressSize != facts.pointerSize ||
        facts.destinationSize != facts.addressSize ||
        facts.elementSize != CHAR_BIT || !facts.fillIsConcrete)
    {
        return false;
    }

    const ConstantValue elementBytes = facts.elementSize / CHAR_BIT;
    if (facts.stride <= 0 ||
        static_cast<ConstantValue>(facts.stride) != elementBytes ||
        !facts.countIsConcrete || facts.count == 0 ||
        facts.count > (std::numeric_limits<ConstantValue>::max)() /
                          elementBytes)
    {
        return false;
    }

    const ConstantValue byteCount = facts.count * elementBytes;
    const ConstantValue pointerMax = bitMask<ConstantValue>(facts.pointerSize);
    if (byteCount > pointerMax || !facts.destinationIsConcrete ||
        facts.destinationMayBeStackOffset || facts.destination > pointerMax ||
        byteCount - 1 > pointerMax - facts.destination ||
        facts.destination > static_cast<ConstantValue>(
            (std::numeric_limits<ByteAddr>::max)()))
    {
        return false;
    }

    if (!facts.hasContainingSection || !facts.sectionIsAllocated ||
        !facts.sectionIsWritable || facts.sectionIsExecutable ||
        facts.sectionAddress < 0 || facts.sectionSize <= 0)
    {
        return false;
    }

    const ByteAddr signedDestination =
        static_cast<ByteAddr>(facts.destination);
    if (signedDestination < facts.sectionAddress) {
        return false;
    }

    const ConstantValue offsetInSection = facts.destination -
        static_cast<ConstantValue>(facts.sectionAddress);
    const ConstantValue sectionSize =
        static_cast<ConstantValue>(facts.sectionSize);
    return offsetInSection <= sectionSize &&
        byteCount <= sectionSize - offsetInSection;
}

} // namespace idiom
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
