/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

/* * SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
 * Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
 * Alexander Fokin, Sergey Levin, Leonid Tsvetkov
 *
 * This file is part of SmartDec decompiler.
 *
 * SmartDec decompiler is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SmartDec decompiler is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include <nc/config.h>

#include <cassert>
#include <cstddef>

#include <nc/common/Types.h>

#include "AbstractValue.h"
#include "DataflowStatus.h"

namespace nc {
namespace core {
namespace ir {
namespace dflow {

/**
 * Dataflow information about a term.
 */
class Value {
    std::size_t *revision_; ///< Revision of the owning dataflow, if any.
    DataflowStatus *analysisStatus_; ///< Lifecycle state of the owning dataflow, if any.

    AbstractValue abstractValue_; ///< Abstract value of the term, in the host byte order.

    bool isStackOffset_; ///< Stack-derived evidence is present.
    bool isNotStackOffset_; ///< Non-stack-derived or conflicting evidence is present.

    SignedConstantValue stackOffset_; ///< Offset to stack frame base (in bytes), if the value is a stack pointer.

    bool isProduct_; ///< Value was computed via multiplication.
    bool isNotProduct_; ///< Value was computed not via multiplication.

    bool isReturnAddress_; ///< Value is a return address.
    bool isNotReturnAddress_; ///< Value is not a return address.

public:
    /**
     * Class constructor.
     *
     * \param size Size of the term.
     */
    explicit Value(SmallBitSize size, std::size_t *revision = nullptr,
                   DataflowStatus *analysisStatus = nullptr);

    /**
     * \return Abstract value of the term.
     */
    const AbstractValue &abstractValue() const { return abstractValue_; }

    /**
     * Sets the abstract value of the term.
     *
     * \param value New abstract value.
     *
     * The value is resized to the size given to constructor of this class.
     */
    void setAbstractValue(AbstractValue value);

    /**
     * \return True if the value is stack pointer with a known offset
     *         from the frame base, false otherwise.
     */
    bool isStackOffset() const { return isStackOffset_ && !isNotStackOffset_; }

    /**
     * \return False only when the value is proved to be exclusively
     *         non-stack-derived. Unknown values and conflicting reaching
     *         values must conservatively be treated as possible frame
     *         pointers by alias-sensitive clients.
     */
    bool mayBeStackOffset() const {
        return isStackOffset_ || !isNotStackOffset_;
    }

    /**
     * \return True if non-stack-derived or conflicting evidence is present.
     *         Use mayBeStackOffset() when making alias-safety decisions.
     */
    bool isNotStackOffset() const { return isNotStackOffset_; }

    /**
     * Marks the value as a stack pointer with a given offset.
     *
     * \param[in] offset Offset to stack frame base.
     */
    void makeStackOffset(SignedConstantValue offset);

    /** Marks the value as stack-derived while discarding an exact offset. */
    void makeAmbiguousStackOffset();

    /**
     * Marks the value as not a stack pointer.
     */
    void makeNotStackOffset();

    /**
     * \return Offset to stack frame base (in bytes), if the value is a stack pointer.
     */
    SignedConstantValue stackOffset() const { assert(isStackOffset()); return stackOffset_; }

    /**
     * \return True, if the value has been computed via multiplication.
     */
    bool isProduct() const { return isProduct_ && !isNotProduct_; }

    /**
     * \return True, if the value has not been computed via multiplication.
     */
    bool isNotProduct() const { return isNotProduct_; }

    /**
     * Marks the value as being computed via multiplication.
     */
    void makeProduct();

    /**
     * Marks the value as being computed not via multiplication.
     */
    void makeNotProduct();

    /**
     * \return True if the value is a return address.
     */
    bool isReturnAddress() const { return isReturnAddress_ && !isNotReturnAddress_; }

    /**
     * \return True if the value is a not return address.
     */
    bool isNotReturnAddress() const { return isNotReturnAddress_; }

    /**
     * Marks the value as being a return address.
     */
    void makeReturnAddress();

    /**
     * Marks the value as being not a return address.
     */
    void makeNotReturnAddress();

private:
    /** Records a semantic state transition in the owning dataflow. */
    void changed() {
        if (revision_) {
            ++*revision_;
        }
        if (analysisStatus_ &&
            *analysisStatus_ == DataflowStatus::CONVERGED)
        {
            *analysisStatus_ = DataflowStatus::INCOMPLETE;
        }
    }
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
