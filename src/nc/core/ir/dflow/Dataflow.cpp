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

#include "Dataflow.h"

#include <vector>

#include <nc/common/Foreach.h>
#include <nc/core/ir/Statement.h>

#include "Value.h"

namespace nc {
namespace core {
namespace ir {
namespace dflow {

Dataflow::Dataflow():
    memoryLocationRevision_(0), valueRevision_(0),
    analysisStatus_(DataflowStatus::INCOMPLETE)
{}

Dataflow::~Dataflow() {}

Value *Dataflow::getValue(const Term *term) {
    assert(term != nullptr);

    if (auto source = term->source()) {
        term = source;
    }

    auto &result = term2value_[term];
    if (!result) {
        result.reset(new Value(term->size(), &valueRevision_, &analysisStatus_));
        ++valueRevision_;
        invalidateAnalysis();
    }
    return result.get();
}

const Value *Dataflow::getValue(const Term *term) const {
    return findValue(term);
}

const Value *Dataflow::findValue(const Term *term) const {
    assert(term != nullptr);

    if (const Term *source = term->source()) {
        term = source;
    }

    const auto position = term2value_.find(term);
    return position == term2value_.end() ? nullptr : position->second.get();
}

void Dataflow::discardDetachedFacts() {
    const auto isDetachedTerm = [](const Term *term) {
        return term->statement() && !term->statement()->basicBlock();
    };

    std::vector<const Term *> detachedLocations;
    foreach (const auto &termAndLocation, term2location_) {
        if (isDetachedTerm(termAndLocation.first)) {
            detachedLocations.push_back(termAndLocation.first);
        }
    }

    foreach (auto &termAndDefinitions, term2definitions_) {
        termAndDefinitions.second.filterOut(
            [isDetachedTerm](const MemoryLocation &, const Term *definition) {
                return isDetachedTerm(definition);
            });
    }

    for (auto iterator = term2value_.begin(); iterator != term2value_.end();) {
        if (isDetachedTerm(iterator->first)) {
            const auto position = iterator++;
            term2value_.erase(position);
        } else {
            ++iterator;
        }
    }
    foreach (const Term *term, detachedLocations) {
        eraseMemoryLocation(term);
    }
    for (auto iterator = term2definitions_.begin();
         iterator != term2definitions_.end();)
    {
        if (isDetachedTerm(iterator->first)) {
            const auto position = iterator++;
            term2definitions_.erase(position);
        } else {
            ++iterator;
        }
    }
    for (auto iterator = statement2definitions_.begin();
         iterator != statement2definitions_.end();)
    {
        if (!iterator->first->basicBlock()) {
            const auto position = iterator++;
            statement2definitions_.erase(position);
        } else {
            ++iterator;
        }
    }
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
