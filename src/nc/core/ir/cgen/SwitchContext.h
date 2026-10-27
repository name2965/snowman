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

#include <boost/unordered_map.hpp>

namespace nc {
namespace core {

namespace likec {
    class IntegerType;
}

namespace ir {

class BasicBlock;

namespace cgen {

/**
 * This class remembers which case labels must be generated for which basic
 * blocks.  Unresolved jump-table entries are retained separately by address.
 */
class SwitchContext {
public:
    typedef boost::unordered_map<const BasicBlock *,
                                 std::vector<ConstantValue>> CaseValuesMap;
    typedef boost::unordered_map<ByteAddr,
                                 std::vector<ConstantValue>> AddressCaseValuesMap;

private:
    /** Type of the value switch upon. */
    const likec::IntegerType *valueType_;

    /** Mapping from a basic block to the corresponding case values. */
    CaseValuesMap caseValuesMap_;

    /** Cases whose jump-table destination could not be resolved to a block. */
    AddressCaseValuesMap addressCaseValuesMap_;

    /** Basic block corresponding to the default case label. */
    const BasicBlock *defaultBasicBlock_;

public:
    /**
     * Default constructor.
     */
    SwitchContext(): valueType_(nullptr), defaultBasicBlock_(nullptr) {}

    /**
     * \return Pointer to the type of the value switched upon. Can be nullptr, if not set.
     */
    const likec::IntegerType *valueType() const { return valueType_; }

    /**
     * Sets the type of the value switched upon.
     *
     * \param[in] type Pointer to the type. Can be nullptr.
     */
    void setValueType(const likec::IntegerType *type) { valueType_ = type; }

    /**
     * \return Pointer to the basic block which must be labeled by default case label. Can be nullptr.
     */
    const BasicBlock *defaultBasicBlock() { return defaultBasicBlock_; }

    /**
     * Sets the basic block that must be labeled by default case label.
     *
     * \param basicBlock Pointer to the basic block. Can be nullptr.
     */
    void setDefaultBasicBlock(const BasicBlock *basicBlock) { defaultBasicBlock_ = basicBlock; }

    /**
     * \return Mapping from a basic block to its corresponding case values.
     */
    const CaseValuesMap &caseValuesMap() { return caseValuesMap_; }

    /**
     * Adds a case value.
     *
     * \param[in] basicBlock Basic block the value corresponds to.
     * \param[in] value      Case value.
     */
    void addCaseValue(const BasicBlock *basicBlock, ConstantValue value) {
        assert(basicBlock != nullptr);
        caseValuesMap_[basicBlock].push_back(value);
    }

    /** Records a case whose destination has no BasicBlock. */
    void addAddressCaseValue(ByteAddr address, ConstantValue value) {
        addressCaseValuesMap_[address].push_back(value);
    }

    /**
     * \param[in] basicBlock A basic block.
     *
     * \return Vector of case values for this basic block.
     */
    const std::vector<ConstantValue> getCaseValues(
            const BasicBlock *basicBlock) {
        assert(basicBlock != nullptr);
        return nc::find(caseValuesMap_, basicBlock);
    }

    /**
     * Forgets the case values for the given basic block.
     *
     * \param[in] basicBlock A basic block.
     */
    void eraseCaseValues(const BasicBlock *basicBlock) {
        assert(basicBlock != nullptr);
        caseValuesMap_.erase(basicBlock);
    }

    const AddressCaseValuesMap &addressCaseValuesMap() const {
        return addressCaseValuesMap_;
    }
};

} // namespace cgen
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
