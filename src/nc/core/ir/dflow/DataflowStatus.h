/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

namespace nc {
namespace core {
namespace ir {
namespace dflow {

/** Lifecycle state of an abstract-interpretation result. */
enum class DataflowStatus {
    /** The analyzer is iterating and facts are provisional. */
    RUNNING,

    /** A fixpoint was reached and semantic clients may consume the facts. */
    CONVERGED,

    /** No analysis is running and no complete fixpoint is available. */
    INCOMPLETE
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
