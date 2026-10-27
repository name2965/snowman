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

#include "Value.h"

#include <nc/common/BitTwiddling.h>
#include <nc/common/Unused.h>

namespace nc {
namespace core {
namespace ir {
namespace dflow {

#ifndef NDEBUG
namespace {

bool testBitTwiddling() {
    {
        int value = 0xf;
        assert(signExtend(value, 4) == -1);
    }

    {
        int value = 0x4;
        assert(signExtend(value, 5) == 4);
    }

    {
        int value = 0x3;
        assert(bitAbs(value, 2) == 1);
    }

    {
        int value = 0x3;
        assert(bitAbs(value, 10) == 3);
    }

    {
        unsigned value = -1;
        assert(bitTruncate(value, 5) == 0x1f);
    }

    {
        unsigned value = -1;
        assert(bitTruncate(value, sizeof(value) * CHAR_BIT) == value);
    }

    return true;
}

bool bitTwiddlingWorks = (NC_UNUSED(bitTwiddlingWorks), testBitTwiddling());

} // anonymous namespace
#endif

Value::Value(SmallBitSize size, std::size_t *revision,
             DataflowStatus *analysisStatus):
    revision_(revision), analysisStatus_(analysisStatus),
    abstractValue_(size, -1, -1),
    isStackOffset_(false), isNotStackOffset_(false),
    isProduct_(false), isNotProduct_(false),
    isReturnAddress_(false), isNotReturnAddress_(false)
{}

void Value::setAbstractValue(AbstractValue value) {
    value.resize(abstractValue_.size());
    if (abstractValue_.size() != value.size() ||
        abstractValue_.zeroBits() != value.zeroBits() ||
        abstractValue_.oneBits() != value.oneBits())
    {
        abstractValue_ = value;
        changed();
    }
}

void Value::makeStackOffset(SignedConstantValue offset) {
    if (isStackOffset_) {
        if (isNotStackOffset_ || stackOffset_ != offset) {
            /* Distinct reaching offsets do not have a sound single-value
             * representative.  Preserve only stack-derived provenance. */
            makeAmbiguousStackOffset();
        }
    } else {
        isStackOffset_ = true;
        stackOffset_ = offset;
        changed();
    }
}

void Value::makeAmbiguousStackOffset() {
    if (!isStackOffset_ || !isNotStackOffset_) {
        isStackOffset_ = true;
        isNotStackOffset_ = true;
        changed();
    }
}

void Value::makeNotStackOffset() {
    if (!isNotStackOffset_) {
        isNotStackOffset_ = true;
        changed();
    }
}

void Value::makeProduct() {
    if (!isProduct_) {
        isProduct_ = true;
        changed();
    }
}

void Value::makeNotProduct() {
    if (!isNotProduct_) {
        isNotProduct_ = true;
        changed();
    }
}

void Value::makeReturnAddress() {
    if (!isReturnAddress_) {
        isReturnAddress_ = true;
        changed();
    }
}

void Value::makeNotReturnAddress() {
    if (!isNotReturnAddress_) {
        isNotReturnAddress_ = true;
        changed();
    }
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
