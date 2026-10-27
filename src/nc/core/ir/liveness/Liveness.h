/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <boost/unordered_set.hpp>

#include <nc/common/Range.h>

namespace nc {
namespace core {
namespace ir {

class Term;

namespace liveness {

/**
 * Set of terms producing actual high-level code.
 */
class Liveness {
    boost::unordered_set<const Term *> liveTermSet_; ///< The set of live terms.
    std::vector<const Term *> liveTermList_; ///< The list of live terms.

    /**
     * Live definitions which have a semantic consumer that is not represented
     * by an ordinary read Term.  Such definitions must remain materialized at
     * their original program point and cannot be replaced solely at their
     * term uses.
     */
    boost::unordered_set<const Term *> materializedTermSet_;

public:
    /**
     * \param[in] term Term.
     *
     * \return True if term is live.
     */
    bool isLive(const Term *term) const {
        assert(term != nullptr);
        return nc::contains(liveTermSet_, term);
    }

    /**
     * Marks a term as live.
     *
     * \param[in] term Valid pointer to a term.
     */
    void makeLive(const Term *term) {
        assert(term != nullptr);

        if (liveTermSet_.insert(term).second) {
            liveTermList_.push_back(term);
        };
    }

    /**
     * Requires a live term to remain materialized at its original program
     * point.  This records non-Term observations without changing ordinary
     * liveness propagation.
     */
    void requireMaterialization(const Term *term) {
        assert(term != nullptr);
        assert(isLive(term));
        materializedTermSet_.insert(term);
    }

    /**
     * \return True if the term has a semantic consumer which requires it to
     *         remain materialized at its original program point.
     */
    bool mustBeMaterialized(const Term *term) const {
        assert(term != nullptr);
        return nc::contains(materializedTermSet_, term);
    }

    /**
     * \return The list of live terms, sorted by the order of adding.
     *
     * \note The ordering is important: type reconstruction completes
     *       much faster if the terms are processed in the natural order.
     */
    const std::vector<const Term *> &liveTerms() const { return liveTermList_; }
};

} // namespace liveness
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
