/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "Dominators.h"

#include <algorithm>
#include <iterator>

#include <boost/unordered_set.hpp>

#include <nc/common/CancellationToken.h>
#include <nc/common/Foreach.h>

#include "BasicBlock.h"
#include "CFG.h"
#include "Function.h"

namespace nc {
namespace core {
namespace ir {

namespace {

const BasicBlock *inferEntry(const CFG &cfg) {
    if (cfg.basicBlocks().empty()) {
        return nullptr;
    }

    const BasicBlock *first = cfg.basicBlocks().front();
    const BasicBlock *functionEntry =
        first->function() ? first->function()->entry() : nullptr;
    if (functionEntry &&
        std::find(cfg.basicBlocks().begin(), cfg.basicBlocks().end(),
                  functionEntry) != cfg.basicBlocks().end())
    {
        return functionEntry;
    }
    return first;
}

} // anonymous namespace

Dominators::Dominators(const CFG &cfg, const CancellationToken &canceled):
    Dominators(cfg, canceled, inferEntry(cfg))
{}

Dominators::Dominators(const CFG &cfg, const CancellationToken &canceled,
                       const BasicBlock *entry): entry_(entry) {
    if (cfg.basicBlocks().empty()) {
        entry_ = nullptr;
        return;
    }

    boost::unordered_set<const BasicBlock *> allBlocks(
        cfg.basicBlocks().begin(), cfg.basicBlocks().end());
    if (!entry || allBlocks.find(entry) == allBlocks.end()) {
        entry_ = nullptr;
        foreach (const BasicBlock *block, cfg.basicBlocks()) {
            dominators_[block].push_back(block);
        }
        return;
    }

    /*
     * Dominators are a greatest fixed point.  Initializing every block with
     * just itself and growing the sets computes the wrong fixed point for
     * cycles: an internal cycle can prevent the function entry from ever
     * reaching its members.  Start reachable non-entry blocks at the top
     * element instead and monotonically shrink by predecessor intersection.
     */
    boost::unordered_set<const BasicBlock *> reachable;
    std::vector<const BasicBlock *> worklist(1, entry);
    reachable.insert(entry);
    while (!worklist.empty()) {
        const BasicBlock *block = worklist.back();
        worklist.pop_back();
        foreach (const BasicBlock *successor, cfg.getSuccessors(block)) {
            if (allBlocks.find(successor) == allBlocks.end()) {
                /* A detached edge cannot participate in this CFG's
                 * dominance relation.  Ignore it instead of manufacturing a
                 * map entry which getDominators() can never query safely. */
                continue;
            }
            if (reachable.insert(successor).second) {
                worklist.push_back(successor);
            }
        }
    }

    std::vector<const BasicBlock *> reachableBlocks;
    foreach (const BasicBlock *block, cfg.basicBlocks()) {
        if (reachable.find(block) != reachable.end()) {
            reachableBlocks.push_back(block);
        }
    }
    const std::less<const BasicBlock *> less;
    std::sort(reachableBlocks.begin(), reachableBlocks.end(), less);

    foreach (const BasicBlock *block, cfg.basicBlocks()) {
        if (block == entry) {
            dominators_[block].push_back(block);
        } else if (reachable.find(block) != reachable.end()) {
            dominators_[block] = reachableBlocks;
        } else {
            /* Keep queries on detached/unreachable blocks conservative. */
            dominators_[block].push_back(block);
        }
    }

    bool changed;
    do {
        changed = false;

        foreach (const BasicBlock *block, cfg.basicBlocks()) {
            if (block == entry || reachable.find(block) == reachable.end()) {
                continue;
            }

            std::vector<const BasicBlock *> newDominators;
            bool haveReachablePredecessor = false;
            foreach (const BasicBlock *predecessor,
                     cfg.getPredecessors(block)) {
                if (reachable.find(predecessor) == reachable.end()) {
                    continue;
                }

                if (!haveReachablePredecessor) {
                    newDominators = dominators_[predecessor];
                    haveReachablePredecessor = true;
                } else {
                    std::vector<const BasicBlock *> intersection;
                    std::set_intersection(
                        newDominators.begin(), newDominators.end(),
                        dominators_[predecessor].begin(),
                        dominators_[predecessor].end(),
                        std::back_inserter(intersection), less);
                    newDominators.swap(intersection);
                }
            }

            if (!haveReachablePredecessor) {
                newDominators.clear();
            }
            newDominators.push_back(block);
            std::sort(newDominators.begin(), newDominators.end(), less);
            newDominators.erase(
                std::unique(newDominators.begin(), newDominators.end()),
                newDominators.end());

            auto &oldDominators = dominators_[block];
            if (newDominators != oldDominators) {
                oldDominators.swap(newDominators);
                changed = true;
            }
        }

        canceled.poll();
    } while (changed);
}

} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
