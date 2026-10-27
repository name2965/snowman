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
}

namespace effects {

/**
 * Architecture-neutral observable effects of evaluating an IR expression.
 *
 * This separates semantic safety from individual pattern recognizers.  It is
 * deliberately conservative: unresolved/user-domain reads are observable,
 * dereferences can trap, and intrinsic leaves are not speculatively
 * repeatable even though discarding an unused intrinsic value is harmless.
 */
class ExpressionEffects {
    bool readsObservableState_;
    bool mayTrap_;
    bool isNonrepeatable_;

public:
    ExpressionEffects():
        readsObservableState_(false), mayTrap_(false),
        isNonrepeatable_(false)
    {}

    static ExpressionEffects analyze(const Term *term,
                                     const dflow::Dataflow &dataflow);

    bool readsObservableState() const { return readsObservableState_; }
    bool mayTrap() const { return mayTrap_; }
    bool isNonrepeatable() const { return isNonrepeatable_; }

    /** True when omitting evaluation cannot remove an observable event. */
    bool canDiscard() const {
        return !readsObservableState_ && !mayTrap_;
    }

    /**
     * True when moving an evaluation across a zero-trip boundary is safe.
     * This is stronger than canDiscard because an intrinsic may stand for a
     * value sampled at a particular program point.
     */
    bool canEvaluateSpeculatively() const {
        return canDiscard() && !isNonrepeatable_;
    }

    void merge(const ExpressionEffects &other) {
        readsObservableState_ =
            readsObservableState_ || other.readsObservableState_;
        mayTrap_ = mayTrap_ || other.mayTrap_;
        isNonrepeatable_ = isNonrepeatable_ || other.isNonrepeatable_;
    }

private:
    static ExpressionEffects analyzeImpl(
        const Term *term, const dflow::Dataflow &dataflow);

    void setReadsObservableState() { readsObservableState_ = true; }
    void setMayTrap() { mayTrap_ = true; }
    void setNonrepeatable() { isNonrepeatable_ = true; }
};

} // namespace effects
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
