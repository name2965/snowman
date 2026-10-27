/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cassert>
#include <vector>

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/Range.h>

namespace nc {

class CancellationToken;

namespace core {
namespace ir {

class BasicBlock;
class CFG;

/**
 * Postdominator sets for a control-flow graph with a synthetic exit.
 *
 * Every graph sink and every block with a control-flow edge leaving the CFG
 * is connected to one conceptual synthetic exit.  The synthetic node is not
 * exposed in the returned sets.  Consequently, two branches which terminate
 * at different exits can have no common real postdominator.
 *
 * Blocks from which no real exit is reachable are deliberately assigned only
 * themselves as postdominators.  This prevents a closed loop or a detached
 * non-terminating component from manufacturing postdominance facts.
 */
class PostDominators {
    /** Blocks with at least one edge to the conceptual synthetic exit. */
    std::vector<const BasicBlock *> exits_;

    /** Blocks from which one of exits_ is reachable. */
    boost::unordered_set<const BasicBlock *> exitReachable_;

    /** Mapping from a basic block to its real postdominators. */
    boost::unordered_map<const BasicBlock *,
                         std::vector<const BasicBlock *>> postdominators_;

public:
    /**
     * Computes postdominators using the classic greatest-fixed-point
     * algorithm on the CFG extended with one synthetic exit.
     */
    PostDominators(const CFG &cfg, const CancellationToken &canceled);

    /**
     * \return Blocks with an edge to the conceptual synthetic exit.
     * A block can be present even when it also has an ordinary CFG successor.
     */
    const std::vector<const BasicBlock *> &exits() const { return exits_; }

    /** Returns whether the block can reach an actual CFG exit. */
    bool canReachExit(const BasicBlock *basicBlock) const {
        return basicBlock != nullptr &&
            exitReachable_.find(basicBlock) != exitReachable_.end();
    }

    /** Returns the sorted set of real postdominators of a block. */
    const std::vector<const BasicBlock *> &getPostDominators(
            const BasicBlock *basicBlock) const {
        assert(basicBlock != nullptr);
        assert(nc::contains(postdominators_, basicBlock));
        return nc::find(postdominators_, basicBlock);
    }

    /** Returns whether \p postdominating postdominates \p postdominated. */
    bool isPostDominating(const BasicBlock *postdominating,
                          const BasicBlock *postdominated) const;

    /**
     * Returns the closest strict real postdominator, or nullptr when none is
     * known.  In particular, exits and exit-unreachable blocks have none.
     */
    const BasicBlock *getImmediatePostDominator(
        const BasicBlock *basicBlock) const;

    /**
     * Returns the closest common real postdominator of all supplied blocks.
     * Returns nullptr for an empty set, for an exit-unreachable input, or when
     * the only common postdominator is the conceptual synthetic exit.
     */
    const BasicBlock *getNearestCommonPostDominator(
        const std::vector<const BasicBlock *> &basicBlocks) const;
};

} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
