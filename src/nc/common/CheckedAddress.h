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
#include <nc/common/Types.h>

#include <limits>

namespace nc {

/**
 * A byte-address interval whose exclusive end is representable by ByteAddr.
 *
 * Snowman's address and size types are signed.  Addresses received from file
 * formats and debugger APIs are commonly unsigned, so they must not be cast
 * until both endpoints have been proved representable.
 */
struct CheckedByteRange {
    ByteAddr begin;
    ByteAddr end;
    ByteSize size;
};

/**
 * Return whether both ranges are well formed and inner is wholly contained
 * in outer.  Empty ranges at either endpoint are permitted.
 */
inline bool containsByteRange(const CheckedByteRange &outer,
                              const CheckedByteRange &inner) {
    return outer.begin >= 0 && outer.begin <= outer.end &&
        outer.size == outer.end - outer.begin &&
        inner.begin >= 0 && inner.begin <= inner.end &&
        inner.size == inner.end - inner.begin &&
        outer.begin <= inner.begin && inner.end <= outer.end;
}

/**
 * Convert an unsigned start and size to a checked half-open byte range.
 * Empty ranges are accepted.  On failure, result is left unchanged.
 */
inline bool checkedByteRange(ConstantValue start, ConstantValue size,
                             CheckedByteRange &result) {
    const ConstantValue maximum = static_cast<ConstantValue>(
        (std::numeric_limits<ByteAddr>::max)());
    if (start > maximum || size > maximum || size > maximum - start) {
        return false;
    }

    CheckedByteRange checked = {
        static_cast<ByteAddr>(start),
        static_cast<ByteAddr>(start + size),
        static_cast<ByteSize>(size)
    };
    result = checked;
    return true;
}

/**
 * Convert an unsigned inclusive interval to a checked half-open byte range.
 * The inclusive end itself is insufficient: end + 1 must also be
 * representable because Snowman's disassembly and section APIs use an
 * exclusive upper bound.  On failure, result is left unchanged.
 */
inline bool checkedInclusiveByteRange(ConstantValue start,
                                      ConstantValue inclusiveEnd,
                                      CheckedByteRange &result) {
    const ConstantValue maximum = static_cast<ConstantValue>(
        (std::numeric_limits<ByteAddr>::max)());
    if (start > inclusiveEnd || inclusiveEnd >= maximum) {
        return false;
    }

    return checkedByteRange(start, inclusiveEnd - start + 1, result);
}

/**
 * Add an unsigned offset to an unsigned address and convert the result to
 * ByteAddr without unsigned wrap or implementation-defined narrowing.
 * On failure, result is left unchanged.
 */
inline bool checkedByteAddressAdd(ConstantValue base, ConstantValue offset,
                                  ByteAddr &result) {
    const ConstantValue maximum = static_cast<ConstantValue>(
        (std::numeric_limits<ByteAddr>::max)());
    if (base > maximum || offset > maximum - base) {
        return false;
    }

    result = static_cast<ByteAddr>(base + offset);
    return true;
}

} // namespace nc

/* vim:set et sts=4 sw=4: */
