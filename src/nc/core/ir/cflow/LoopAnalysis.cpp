/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "LoopAnalysis.h"

#include <algorithm>
#include <cassert>
#include <utility>

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/Foreach.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>

namespace nc {
namespace core {
namespace ir {
namespace cflow {

namespace {

typedef boost::unordered_set<const BasicBlock *> BlockSet;

struct LoopCandidate {
    const BasicBlock *header;
    BlockSet latches;
    BlockSet blocks;
    bool reducible;

    LoopCandidate(): header(nullptr), reducible(true) {}
};

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

BlockSet getReachableBlocks(const CFG &cfg, const BasicBlock *entry,
                            const BlockSet &allBlocks) {
    BlockSet result;
    if (!entry || allBlocks.find(entry) == allBlocks.end()) {
        return result;
    }

    std::vector<const BasicBlock *> worklist(1, entry);
    result.insert(entry);
    while (!worklist.empty()) {
        const BasicBlock *block = worklist.back();
        worklist.pop_back();

        foreach (const BasicBlock *successor, cfg.getSuccessors(block)) {
            if (allBlocks.find(successor) == allBlocks.end()) {
                continue;
            }
            if (result.insert(successor).second) {
                worklist.push_back(successor);
            }
        }
    }
    return result;
}

void addBackEdge(LoopCandidate &candidate, const BasicBlock *latch,
                 const CFG &cfg, const Dominators &dominators,
                 const BlockSet &reachable) {
    candidate.latches.insert(latch);
    candidate.blocks.insert(candidate.header);

    std::vector<const BasicBlock *> worklist;
    if (candidate.blocks.insert(latch).second && latch != candidate.header) {
        worklist.push_back(latch);
    }

    /*
     * Compute the classic reverse predecessor closure.  A node in a natural
     * loop must be dominated by the header.  Encountering any other node
     * proves that the cycle has an additional entry and is irreducible.
     */
    while (!worklist.empty()) {
        const BasicBlock *block = worklist.back();
        worklist.pop_back();

        foreach (const BasicBlock *predecessor, cfg.getPredecessors(block)) {
            if (reachable.find(predecessor) == reachable.end()) {
                continue;
            }
            if (predecessor != candidate.header &&
                !dominators.isDominating(candidate.header, predecessor))
            {
                candidate.reducible = false;
                continue;
            }

            if (candidate.blocks.insert(predecessor).second &&
                predecessor != candidate.header)
            {
                worklist.push_back(predecessor);
            }
        }
    }
}

bool hasSingleEntry(const LoopCandidate &candidate, const CFG &cfg,
                    const BlockSet &reachable) {
    foreach (const BasicBlock *block, candidate.blocks) {
        if (block == candidate.header) {
            continue;
        }
        foreach (const BasicBlock *predecessor, cfg.getPredecessors(block)) {
            if (reachable.find(predecessor) != reachable.end() &&
                candidate.blocks.find(predecessor) == candidate.blocks.end()) {
                return false;
            }
        }
    }
    return true;
}

const BasicBlock *findPreheader(const LoopCandidate &candidate, const CFG &cfg,
                                const BlockSet &reachable) {
    BlockSet outsidePredecessors;
    foreach (const BasicBlock *predecessor,
             cfg.getPredecessors(candidate.header))
    {
        if (reachable.find(predecessor) != reachable.end() &&
            candidate.blocks.find(predecessor) == candidate.blocks.end()) {
            outsidePredecessors.insert(predecessor);
        }
    }
    if (outsidePredecessors.size() != 1) {
        return nullptr;
    }

    const BasicBlock *preheader = *outsidePredecessors.begin();
    BlockSet distinctSuccessors;
    foreach (const BasicBlock *successor, cfg.getSuccessors(preheader)) {
        distinctSuccessors.insert(successor);
    }
    return distinctSuccessors.size() == 1 &&
           *distinctSuccessors.begin() == candidate.header ? preheader : nullptr;
}

} // anonymous namespace

bool NaturalLoop::contains(const BasicBlock *basicBlock) const {
    return std::find(blocks_.begin(), blocks_.end(), basicBlock) != blocks_.end();
}

LoopAnalysis::LoopAnalysis(const CFG &cfg, const Dominators &dominators) {
    analyze(cfg, dominators, inferEntry(cfg));
}

LoopAnalysis::LoopAnalysis(const CFG &cfg, const Dominators &dominators,
                           const BasicBlock *entry) {
    analyze(cfg, dominators, entry);
}

const NaturalLoop *LoopAnalysis::getLoop(const BasicBlock *basicBlock) const {
    foreach (const NaturalLoop &loop, loops_) {
        if (loop.header() == basicBlock) {
            return &loop;
        }
    }
    return nullptr;
}

void LoopAnalysis::analyze(const CFG &cfg, const Dominators &dominators,
                           const BasicBlock *entry) {
    loops_.clear();

    /* Mixing analyses rooted at different entries silently corrupts the
     * back-edge test. Invalid/mismatched inputs conservatively produce no
     * loop facts instead of turning a stale entry pointer into an assertion. */
    if (!entry || dominators.entry() != entry) {
        return;
    }

    BlockSet allBlocks(cfg.basicBlocks().begin(), cfg.basicBlocks().end());
    const BlockSet reachable = getReachableBlocks(cfg, entry, allBlocks);
    if (reachable.empty()) {
        return;
    }

    boost::unordered_map<const BasicBlock *, LoopCandidate> candidates;

    foreach (const BasicBlock *latch, cfg.basicBlocks()) {
        if (reachable.find(latch) == reachable.end()) {
            continue;
        }
        foreach (const BasicBlock *header, cfg.getSuccessors(latch)) {
            if (reachable.find(header) == reachable.end() ||
                !dominators.isDominating(header, latch))
            {
                continue;
            }

            LoopCandidate &candidate = candidates[header];
            candidate.header = header;
            addBackEdge(candidate, latch, cfg, dominators, reachable);
        }
    }

    /* Materialize descriptors in CFG order for deterministic output. */
    foreach (const BasicBlock *header, cfg.basicBlocks()) {
        auto position = candidates.find(header);
        if (position == candidates.end()) {
            continue;
        }

        const LoopCandidate &candidate = position->second;
        if (!candidate.reducible ||
            !hasSingleEntry(candidate, cfg, reachable)) {
            continue;
        }

        NaturalLoop loop;
        loop.header_ = candidate.header;
        loop.preheader_ = findPreheader(candidate, cfg, reachable);

        foreach (const BasicBlock *block, cfg.basicBlocks()) {
            if (candidate.blocks.find(block) != candidate.blocks.end()) {
                loop.blocks_.push_back(block);
            }
            if (candidate.latches.find(block) != candidate.latches.end()) {
                loop.latches_.push_back(block);
            }
        }

        foreach (const BasicBlock *source, loop.blocks_) {
            BlockSet seenTargets;
            foreach (const BasicBlock *target, cfg.getSuccessors(source)) {
                if (candidate.blocks.find(target) == candidate.blocks.end() &&
                    seenTargets.insert(target).second)
                {
                    loop.exits_.push_back(LoopExit(source, target));
                }
            }
        }

        loops_.push_back(std::move(loop));
    }
}

} // namespace cflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
