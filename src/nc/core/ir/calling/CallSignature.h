/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <memory>
#include <vector>

#include <nc/core/ir/Term.h>

#include "FunctionPrototype.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

/**
 * Signature of a function: arguments, return value, name.
 */
class CallSignature {
public:
    enum class ArgumentEvidence {
        /** Arguments reconstructed without excluding a fixed prototype. */
        ALL_OBSERVED,

        /** Only arguments beyond an authoritative variadic fixed prefix. */
        VARIADIC_TAIL
    };

private:
    std::vector<std::shared_ptr<const Term>> arguments_; ///< Terms representing the arguments.
    std::shared_ptr<const Term> returnValue_; ///< Terms representing the return value.
    std::shared_ptr<const FunctionPrototype> prototype_; ///< Optional source-level prototype metadata.
    ArgumentEvidence argumentEvidence_ = ArgumentEvidence::ALL_OBSERVED;

public:
    /**
     * \return List of terms representing the arguments.
     */
    std::vector<std::shared_ptr<const Term>> &arguments() { return arguments_; }

    /**
     * \return List of terms representing the arguments.
     */
    const std::vector<std::shared_ptr<const Term>> &arguments() const { return arguments_; }

    ArgumentEvidence argumentEvidence() const { return argumentEvidence_; }
    void setArgumentEvidence(ArgumentEvidence evidence) {
        argumentEvidence_ = evidence;
    }

    /**
     * \return Pointer to the term containing the return value. Can be nullptr.
     */
    const std::shared_ptr<const Term> &returnValue() const { return returnValue_; }

    /**
     * Sets the pointer to the term representing the return value.
     *
     * \param term Valid pointer to the term.
     */
    void setReturnValue(std::shared_ptr<const Term> term) { returnValue_ = std::move(term); }

    /** \return Optional source-level prototype metadata. */
    const std::shared_ptr<const FunctionPrototype> &prototype() const { return prototype_; }

    /** Sets optional source-level prototype metadata. */
    void setPrototype(std::shared_ptr<const FunctionPrototype> prototype) {
        prototype_ = std::move(prototype);
    }
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
