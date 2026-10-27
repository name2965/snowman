/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

namespace nc {
namespace core {
namespace ir {

class Term;

namespace dflow {

class Dataflow;
class DefUseGraph;
class ValueProvenance;

/**
 * Conservatively proves that two scalar IR expressions denote the same
 * execution value.
 *
 * This is deliberately an identity proof rather than an algebraic
 * simplifier.  Constants and operator trees are compared structurally.  A
 * register read is accepted only when both reads name the exact same register
 * range and have the exact same complete, unique reaching definition.  A
 * dereference is accepted only when dataflow resolves both occurrences to the
 * same scalar STACK location and proves the same complete, unique reaching
 * definition.  Other memory and expressions whose value is missing on any
 * CFG path are rejected.
 *
 * The referenced analysis objects and all IR terms must outlive this object.
 * They must describe the same, unmodified IR snapshot.
 */
class ExpressionIdentity {
    const Dataflow &dataflow_;
    const DefUseGraph &defUse_;
    const ValueProvenance &provenance_;

public:
    ExpressionIdentity(const Dataflow &dataflow, const DefUseGraph &defUse,
                       const ValueProvenance &provenance):
        dataflow_(dataflow), defUse_(defUse), provenance_(provenance)
    {}

    /**
     * Returns true only when equality of the two scalar values can be proved
     * from their IR structure and complete reaching-definition provenance.
     */
    bool areIdentical(const Term *left, const Term *right) const;
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
