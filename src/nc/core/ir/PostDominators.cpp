/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "PostDominators.h"

#include <algorithm>
#include <functional>
#include <iterator>

#include <boost/unordered_set.hpp>

#include <nc/common/CancellationToken.h>
#include <nc/common/Foreach.h>

#include "BasicBlock.h"
#include "CFG.h"
#include "Jump.h"
#include "JumpTarget.h"

namespace nc {
namespace core {
namespace ir {

namespace {

/**
 * Returns whether a jump target has a destination outside the CFG.
 *
 * A resolved direct target can retain its address expression, and an indirect
 * table target uses its address expression to locate the table.  Neither
 * expression represents an additional outgoing edge when all actual targets
 * have BasicBlock objects.
 */
bool hasExternalDestination(const JumpTarget &target) {
    bool hasResolvedDestination = target.basicBlock() != nullptr;

    if (const JumpTable *table = target.table()) {
        if (table->empty()) {
            return true;
        }
        foreach (const JumpTableEntry &entry, *table) {
            if (!entry.basicBlock()) {
                return true;
            }
            hasResolvedDestination = true;
        }
    }

    return !hasResolvedDestination && target.address() != nullptr;
}

/** Returns whether a block has an edge to the synthetic exit. */
bool hasSyntheticExitEdge(const BasicBlock *block, const CFG &cfg) {
    assert(block != nullptr);

    const Jump *jump = block->getJump();
    if (jump) {
        if (hasExternalDestination(jump->thenTarget()) ||
            (jump->isConditional() &&
             hasExternalDestination(jump->elseTarget())))
        {
            return true;
        }
    }

    /* Halt, fall-through beyond the function, and other graph sinks. */
    return cfg.getSuccessors(block).empty();
}

} // anonymous namespace

PostDominators::PostDominators(const CFG &cfg,
                               const CancellationToken &canceled) {
    if (cfg.basicBlocks().empty()) {
        return;
    }

    boost::unordered_set<const BasicBlock *> allBlocks(
        cfg.basicBlocks().begin(), cfg.basicBlocks().end());

    foreach (const BasicBlock *block, cfg.basicBlocks()) {
        if (hasSyntheticExitEdge(block, cfg)) {
            exits_.push_back(block);
            exitReachable_.insert(block);
        }
    }

    const std::less<const BasicBlock *> less;
    std::sort(exits_.begin(), exits_.end(), less);

    /* Reverse reachability from every real edge to the synthetic exit. */
    std::vector<const BasicBlock *> worklist(exits_.begin(), exits_.end());
    while (!worklist.empty()) {
        const BasicBlock *block = worklist.back();
        worklist.pop_back();

        foreach (const BasicBlock *predecessor,
                 cfg.getPredecessors(block)) {
            if (allBlocks.find(predecessor) != allBlocks.end() &&
                exitReachable_.insert(predecessor).second)
            {
                worklist.push_back(predecessor);
            }
        }
        canceled.poll();
    }

    std::vector<const BasicBlock *> allSorted(
        cfg.basicBlocks().begin(), cfg.basicBlocks().end());
    std::sort(allSorted.begin(), allSorted.end(), less);

    boost::unordered_set<const BasicBlock *> exitBlocks(
        exits_.begin(), exits_.end());

    /*
     * Postdominators are a greatest fixed point.  Exit-reachable non-exits
     * therefore start at the lattice top and shrink.  A block with a direct
     * synthetic-exit edge has no real postdominator beyond itself.  The same
     * conservative rule is used for blocks which cannot reach an exit.
     */
    foreach (const BasicBlock *block, cfg.basicBlocks()) {
        if (exitReachable_.find(block) == exitReachable_.end() ||
            exitBlocks.find(block) != exitBlocks.end())
        {
            postdominators_[block].push_back(block);
        } else {
            postdominators_[block] = allSorted;
        }
    }

    bool changed;
    do {
        changed = false;

        foreach (const BasicBlock *block, cfg.basicBlocks()) {
            if (exitReachable_.find(block) == exitReachable_.end() ||
                exitBlocks.find(block) != exitBlocks.end())
            {
                continue;
            }

            std::vector<const BasicBlock *> newPostdominators;
            bool haveSuccessor = false;

            foreach (const BasicBlock *successor,
                     cfg.getSuccessors(block)) {
                if (allBlocks.find(successor) == allBlocks.end()) {
                    /* CFG normally filters such edges.  If a custom CFG ever
                     * exposes one, treat it as the synthetic exit. */
                    newPostdominators.clear();
                    haveSuccessor = true;
                    break;
                }

                if (!haveSuccessor) {
                    newPostdominators = postdominators_[successor];
                    haveSuccessor = true;
                } else {
                    std::vector<const BasicBlock *> intersection;
                    std::set_intersection(
                        newPostdominators.begin(),
                        newPostdominators.end(),
                        postdominators_[successor].begin(),
                        postdominators_[successor].end(),
                        std::back_inserter(intersection), less);
                    newPostdominators.swap(intersection);
                }
            }

            /* A non-exit marked reachable must have an ordinary successor. */
            if (!haveSuccessor) {
                newPostdominators.clear();
            }
            newPostdominators.push_back(block);
            std::sort(newPostdominators.begin(),
                      newPostdominators.end(), less);
            newPostdominators.erase(
                std::unique(newPostdominators.begin(),
                            newPostdominators.end()),
                newPostdominators.end());

            std::vector<const BasicBlock *> &oldPostdominators =
                postdominators_[block];
            if (newPostdominators != oldPostdominators) {
                oldPostdominators.swap(newPostdominators);
                changed = true;
            }
        }

        canceled.poll();
    } while (changed);
}

bool PostDominators::isPostDominating(
        const BasicBlock *postdominating,
        const BasicBlock *postdominated) const {
    assert(postdominating != nullptr);
    assert(nc::contains(postdominators_, postdominating));
    assert(postdominated != nullptr);
    assert(nc::contains(postdominators_, postdominated));

    const std::vector<const BasicBlock *> &postdominators =
        getPostDominators(postdominated);
    return std::binary_search(postdominators.begin(),
                              postdominators.end(), postdominating,
                              std::less<const BasicBlock *>());
}

const BasicBlock *PostDominators::getImmediatePostDominator(
        const BasicBlock *basicBlock) const {
    assert(basicBlock != nullptr);
    assert(nc::contains(postdominators_, basicBlock));

    if (!canReachExit(basicBlock)) {
        return nullptr;
    }

    const std::vector<const BasicBlock *> &postdominators =
        getPostDominators(basicBlock);
    foreach (const BasicBlock *candidate, postdominators) {
        if (candidate == basicBlock) {
            continue;
        }

        bool closest = true;
        foreach (const BasicBlock *other, postdominators) {
            if (other != basicBlock && other != candidate &&
                !isPostDominating(other, candidate))
            {
                closest = false;
                break;
            }
        }
        if (closest) {
            return candidate;
        }
    }
    return nullptr;
}

const BasicBlock *PostDominators::getNearestCommonPostDominator(
        const std::vector<const BasicBlock *> &basicBlocks) const {
    if (basicBlocks.empty()) {
        return nullptr;
    }

    std::vector<const BasicBlock *> common;
    bool first = true;
    const std::less<const BasicBlock *> less;

    foreach (const BasicBlock *block, basicBlocks) {
        if (!block || !nc::contains(postdominators_, block) ||
            !canReachExit(block))
        {
            return nullptr;
        }

        if (first) {
            common = getPostDominators(block);
            first = false;
        } else {
            std::vector<const BasicBlock *> intersection;
            const std::vector<const BasicBlock *> &postdominators =
                getPostDominators(block);
            std::set_intersection(
                common.begin(), common.end(),
                postdominators.begin(), postdominators.end(),
                std::back_inserter(intersection), less);
            common.swap(intersection);
        }

        if (common.empty()) {
            return nullptr;
        }
    }

    foreach (const BasicBlock *candidate, common) {
        bool closest = true;
        foreach (const BasicBlock *other, common) {
            if (other != candidate &&
                !isPostDominating(other, candidate))
            {
                closest = false;
                break;
            }
        }
        if (closest) {
            return candidate;
        }
    }
    return nullptr;
}

} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
