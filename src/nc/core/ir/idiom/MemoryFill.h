/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cassert>
#include <climits>
#include <utility>
#include <vector>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace ir {

class BasicBlock;
class Statement;
class Term;

namespace cflow {
    class Region;
}

namespace idiom {

/**
 * Semantic description of a loop that writes the same element value to a
 * contiguous memory range.
 *
 * This descriptor deliberately does not name a source-library routine.  A
 * later lowering stage may choose memset, a typed fill loop, or another
 * representation according to the element value and the target language.
 */
class MemoryFill {
    const BasicBlock *loopHeader_; ///< Header of the natural loop implementing the fill.
    const cflow::Region *region_; ///< Matching structured loop, if available.
    /** Definition holding the destination pointer captured before loop entry. */
    const Term *destination_;
    const Term *elementValue_; ///< Loop-invariant value written per iteration.
    /** Definition holding the iteration count captured before loop entry. */
    const Term *elementCount_;
    SmallBitSize addressSize_; ///< Width of the pointer recurrence, in bits.
    SmallBitSize elementSize_; ///< Size of one written element, in bits.
    SignedConstantValue stride_; ///< Pointer change per iteration, in bytes.
    const Statement *originStatement_; ///< Memory write represented by the idiom.
    std::vector<const Statement *> coveredStatements_; ///< Statements summarized by this operation.

public:
    MemoryFill(const BasicBlock *loopHeader, const cflow::Region *region,
               const Term *destination,
               const Term *elementValue, const Term *elementCount,
               SmallBitSize addressSize, SmallBitSize elementSize,
               SignedConstantValue stride,
               const Statement *originStatement,
               std::vector<const Statement *> coveredStatements):
        loopHeader_(loopHeader), region_(region), destination_(destination),
        elementValue_(elementValue), elementCount_(elementCount),
        addressSize_(addressSize), elementSize_(elementSize), stride_(stride),
        originStatement_(originStatement),
        coveredStatements_(std::move(coveredStatements))
    {
        assert(loopHeader_ != nullptr);
        assert(destination_ != nullptr);
        assert(elementValue_ != nullptr);
        assert(elementCount_ != nullptr);
        assert(addressSize_ > 0);
        assert(elementSize_ > 0 && elementSize_ % CHAR_BIT == 0);
        assert(stride_ != 0);
        assert(originStatement_ != nullptr);
    }

    const BasicBlock *loopHeader() const { return loopHeader_; }
    const cflow::Region *region() const { return region_; }
    const Term *destination() const { return destination_; }
    const Term *elementValue() const { return elementValue_; }
    const Term *elementCount() const { return elementCount_; }
    SmallBitSize addressSize() const { return addressSize_; }
    SmallBitSize elementSize() const { return elementSize_; }
    SignedConstantValue stride() const { return stride_; }
    const Statement *originStatement() const { return originStatement_; }
    const std::vector<const Statement *> &coveredStatements() const {
        return coveredStatements_;
    }
};

} // namespace idiom
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
