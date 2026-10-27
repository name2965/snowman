/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "Patch.h"

#include <limits>
#include <stdexcept>

#include <nc/common/Foreach.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Statement.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

Patch::~Patch() {}

void Patch::insertAfter(Statement *after) {
    assert(after != nullptr);

    /* Reserve all bookkeeping before touching the IR.  Otherwise an
     * allocation failure in push_back() after BasicBlock::insertAfter()
     * would leave an inserted statement which remove() cannot find. */
    if (statements_.size() >
        (std::numeric_limits<std::size_t>::max)() -
            insertedStatements_.size())
    {
        throw std::length_error("patch statement count overflow");
    }
    insertedStatements_.reserve(
        insertedStatements_.size() + statements_.size());

    while (!statements_.empty()) {
        insertedStatements_.push_back(after->basicBlock()->insertAfter(after, statements_.pop_back()));
    }
}

void Patch::remove() {
    foreach (auto statement, insertedStatements_) {
        statements_.push_front(statement->basicBlock()->erase(statement));
    }
    insertedStatements_.clear();
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
