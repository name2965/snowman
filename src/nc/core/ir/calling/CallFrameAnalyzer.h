/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <boost/optional.hpp>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace ir {

class Call;

namespace dflow {
class Dataflow;
}

namespace calling {

class CallHook;
class Convention;

/**
 * Recovers facts about a single machine call frame from stabilized IR.
 *
 * This analysis deliberately recognizes only stack-only, downward-growing
 * calling sequences whose outgoing slots and caller cleanup agree exactly.
 * It does not use symbol names or instruction opcodes.  Failure to prove any
 * of the structural invariants is represented by boost::none.
 */
class CallFrameAnalyzer {
public:
    /**
     * Infers the byte extent of stack arguments discarded by the caller.
     *
     * The result is produced only when:
     *
     *  - dataflow reached a fixpoint and the call hook captured an exact SP;
     *  - the next machine instruction restores SP relative to that exact SP;
     *  - the whole restored range is covered by unambiguous reaching stores;
     *  - every slot store is coupled to a same-instruction SP decrement; and
     *  - no unrelated SP write or call occurs in the setup sequence.
     *
     * The returned extent is call-site evidence.  It must not be promoted to
     * a named calling convention, since identical machine sequences can be
     * produced by multiple source-level ABIs.
     */
    static boost::optional<ByteSize> inferCallerCleanupArgumentSize(
        const Call *call, const Convention *convention,
        const CallHook *hook, const dflow::Dataflow &dataflow);
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
