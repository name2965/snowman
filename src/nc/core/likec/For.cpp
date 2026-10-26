/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "For.h"

#include "Expression.h"

namespace nc {
namespace core {
namespace likec {

void For::doCallOnChildren(const std::function<void(TreeNode *)> &fun) {
    fun(initializer_.get());
    fun(condition_.get());
    fun(increment_.get());
    fun(body_.get());
}

} // namespace likec
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
