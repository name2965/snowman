/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <functional>
#include <vector>

#include <boost/unordered_map.hpp>

#include <nc/common/Range.h>

namespace nc {

class CancellationToken;

namespace core {
namespace ir {

class BasicBlock;
class CFG;

/**
 * Dominator sets.
 */
class Dominators {
    /** Entry used to compute reachable blocks. */
    const BasicBlock *entry_;

    /** Mapping from a basic block to the set of its dominators. */
    boost::unordered_map<const BasicBlock *, std::vector<const BasicBlock *>> dominators_;

public:
    /**
     * Constructs dominator sets from the control flow graph.
     * Uses classic iterative algorithm for that.
     *
     * \param cfg Control flow graph.
     * \param canceled Cancellation token.
     */
    Dominators(const CFG &cfg, const CancellationToken &canceled);

    /**
     * Constructs dominator sets for the subgraph reachable from a specified
     * entry block. Detached blocks are treated conservatively as being
     * dominated only by themselves.
     *
     * \param cfg Control flow graph.
     * \param canceled Cancellation token.
     * \param entry Entry block. If null or outside \p cfg, every block is
     * conservatively treated as dominated only by itself.
     */
    Dominators(const CFG &cfg, const CancellationToken &canceled,
               const BasicBlock *entry);

    /** \return Entry used for this analysis, or nullptr if none was valid. */
    const BasicBlock *entry() const { return entry_; }

    /**
     * \param basicBlock Valid pointer to a basic block.
     *
     * \return The set of dominators of this basic block.
     */
    const std::vector<const BasicBlock *> &getDominators(const BasicBlock *basicBlock) const {
        assert(basicBlock != nullptr);
        assert(nc::contains(dominators_, basicBlock));
        return nc::find(dominators_, basicBlock);
    }

    /**
     * \param dominating Valid pointer to a basic block.
     * \param dominated Valid pointer to a basic block.
     *
     * \return True of dominating dominates dominated.
     */
    bool isDominating(const BasicBlock *dominating, const BasicBlock *dominated) const {
        assert(dominating != nullptr);
        assert(nc::contains(dominators_, dominating));
        assert(dominated != nullptr);
        assert(nc::contains(dominators_, dominated));

        const auto &dominators = getDominators(dominated);
        return std::binary_search(dominators.begin(), dominators.end(), dominating,
                                  std::less<const BasicBlock *>());
    }
};

} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
