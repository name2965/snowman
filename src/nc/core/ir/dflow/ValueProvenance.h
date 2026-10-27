/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cstddef>

#include <boost/unordered_set.hpp>

namespace nc {
namespace core {
namespace ir {

class Dominators;
class CFG;
class Statement;
class Term;

namespace dflow {

class Dataflow;
class DefUseGraph;

/**
 * Proves that every value read by an expression has a definition on every
 * path to that read.
 *
 * ReachingDefinitions explicitly distinguishes bit-range gaps, value-less
 * writes, and function-entry values preserved by CFG alternatives.  A unique
 * definition term still does not prove correct evaluation order or freedom
 * from opaque clobbers.  This class supplies those remaining path proofs by
 * recursively requiring a unique exact definition which dominates each use
 * (and strictly precedes it inside a basic block).
 *
 * This is intentionally a conservative scalar proof.  A dereference is
 * accepted only when it resolves to an exact STACK location with a complete,
 * unique reaching definition; generic memory and explicitly undefined leaves
 * are rejected.  A successful result says nothing about whether evaluating
 * the expression is pure, non-trapping, or representable in a target
 * language; clients must prove those properties separately.
 */
class ValueProvenance {
    const Dataflow &dataflow_;
    const DefUseGraph &defUse_;
    const Dominators &dominators_;
    const CFG &cfg_;

public:
    ValueProvenance(const Dataflow &dataflow, const DefUseGraph &defUse,
                    const Dominators &dominators, const CFG &cfg):
        dataflow_(dataflow), defUse_(defUse), dominators_(dominators),
        cfg_(cfg)
    {}

    /**
     * Returns true iff every scalar leaf of \p term is defined on every CFG
     * path to the statement containing that leaf.  Assignment left-hand-side
     * terms are interpreted as the value assigned by their right-hand side.
     */
    bool isPathComplete(const Term *term) const;

    /**
     * Returns true iff no call or inline-assembly statement with unmodeled
     * register effects can execute between a particular definition and any
     * subsequent dynamic occurrence of a use before that definition is
     * executed again.
     *
     * This is useful for recurrence entry values: their loop read normally
     * has both an entry definition and a back-edge definition, so asking for
     * a globally unique reaching definition would be inappropriate.
     */
    bool isUnclobberedBetween(const Term *definition,
                              const Term *use) const;

private:
    bool isPathCompleteImpl(
        const Term *term, boost::unordered_set<const Term *> &visiting,
        std::size_t depth) const;

    bool definitionPrecedesUse(const Statement *definition,
                               const Statement *use) const;

    /**
     * Returns true if an operation whose register-clobber effects are not
     * represented by reaching definitions can execute after \p definition
     * and before \p use.  The query is statement-sensitive and follows CFG
     * cycles; re-executing the definition resets the path state.
     */
    bool hasOpaqueClobberBetween(const Statement *definition,
                                 const Statement *use) const;
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
