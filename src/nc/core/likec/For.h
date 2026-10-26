/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <memory>

#include "Expression.h"
#include "Statement.h"

namespace nc {
namespace core {
namespace likec {

/**
 * A C-style for loop.
 */
class For: public Statement {
    std::unique_ptr<Expression> initializer_; ///< Loop initializer.
    std::unique_ptr<Expression> condition_; ///< Loop condition.
    std::unique_ptr<Expression> increment_; ///< Loop increment.
    std::unique_ptr<Statement> body_; ///< Loop body.

public:
    /**
     * Class constructor.
     *
     * \param[in] initializer Valid pointer to the loop initializer.
     * \param[in] condition Valid pointer to the loop condition.
     * \param[in] increment Valid pointer to the loop increment.
     * \param[in] body Valid pointer to the loop body.
     */
    For(std::unique_ptr<Expression> initializer,
        std::unique_ptr<Expression> condition,
        std::unique_ptr<Expression> increment,
        std::unique_ptr<Statement> body):
        Statement(FOR), initializer_(std::move(initializer)),
        condition_(std::move(condition)), increment_(std::move(increment)),
        body_(std::move(body))
    {
        assert(initializer_);
        assert(condition_);
        assert(increment_);
        assert(body_);
    }

    std::unique_ptr<Expression> &initializer() { return initializer_; }
    const Expression *initializer() const { return initializer_.get(); }

    std::unique_ptr<Expression> &condition() { return condition_; }
    const Expression *condition() const { return condition_.get(); }

    std::unique_ptr<Expression> &increment() { return increment_; }
    const Expression *increment() const { return increment_.get(); }

    std::unique_ptr<Statement> &body() { return body_; }
    const Statement *body() const { return body_.get(); }

protected:
    void doCallOnChildren(const std::function<void(TreeNode *)> &fun) override;
};

} // namespace likec
} // namespace core
} // namespace nc

NC_SUBCLASS(nc::core::likec::Statement, nc::core::likec::For, nc::core::likec::Statement::FOR)

/* vim:set et sts=4 sw=4: */
