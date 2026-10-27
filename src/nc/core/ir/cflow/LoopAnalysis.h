/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <vector>

namespace nc {
namespace core {
namespace ir {

class BasicBlock;
class CFG;
class Dominators;

namespace cflow {

/**
 * An edge leaving a natural loop.
 */
class LoopExit {
    const BasicBlock *source_; ///< Block inside the loop.
    const BasicBlock *target_; ///< Block outside the loop.

public:
    LoopExit(const BasicBlock *source, const BasicBlock *target):
        source_(source), target_(target)
    {}

    const BasicBlock *source() const { return source_; }
    const BasicBlock *target() const { return target_; }
};

/**
 * A single-entry natural loop.
 *
 * Loops having several back edges to the same header are represented by one
 * object with several latches.  Blocks and latches are stored in CFG order.
 */
class NaturalLoop {
    const BasicBlock *header_; ///< Block dominating every block in the loop.
    std::vector<const BasicBlock *> latches_; ///< Sources of back edges.
    std::vector<const BasicBlock *> blocks_; ///< All loop blocks, including the header.
    std::vector<LoopExit> exits_; ///< Edges from loop blocks to non-loop blocks.
    const BasicBlock *preheader_; ///< Unique dedicated predecessor, if one exists.

public:
    const BasicBlock *header() const { return header_; }
    const std::vector<const BasicBlock *> &latches() const { return latches_; }
    const std::vector<const BasicBlock *> &blocks() const { return blocks_; }
    const std::vector<LoopExit> &exits() const { return exits_; }
    const BasicBlock *preheader() const { return preheader_; }

    /**
     * \return True if basicBlock belongs to this loop.
     */
    bool contains(const BasicBlock *basicBlock) const;

private:
    friend class LoopAnalysis;

    NaturalLoop(): header_(nullptr), preheader_(nullptr) {}
};

/**
 * Discovers reducible natural loops in a control-flow graph.
 *
 * An edge latch -> header is considered a back edge only if header dominates
 * latch.  The reverse predecessor closure of all back edges sharing a header
 * forms one loop.  Candidates with an entry into a non-header block are
 * rejected, so irreducible cycles are deliberately left unstructured.
 */
class LoopAnalysis {
    std::vector<NaturalLoop> loops_;

public:
    /**
     * Constructs loop information, inferring the function entry from the CFG.
     */
    LoopAnalysis(const CFG &cfg, const Dominators &dominators);

    /**
     * Constructs loop information using an explicit CFG entry block.
     *
     * The explicit overload is useful for detached CFGs used by tests and
     * other analyses.  An invalid or null entry produces no loops.
     */
    LoopAnalysis(const CFG &cfg, const Dominators &dominators,
                 const BasicBlock *entry);

    const std::vector<NaturalLoop> &loops() const { return loops_; }

    /**
     * Finds a loop by its header.
     *
     * \return The matching loop, or nullptr when basicBlock is not a header.
     */
    const NaturalLoop *getLoop(const BasicBlock *basicBlock) const;

private:
    void analyze(const CFG &cfg, const Dominators &dominators,
                 const BasicBlock *entry);
};

} // namespace cflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
