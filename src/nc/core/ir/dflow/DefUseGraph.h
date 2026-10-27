/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <vector>

#include <boost/unordered_map.hpp>

#include <nc/core/ir/MemoryLocation.h>

#include "ReachingDefinitions.h"

namespace nc {
namespace core {
namespace ir {

class Term;

namespace dflow {

class Dataflow;

/**
 * A read-to-definitions and definition-to-uses view of dataflow results.
 *
 * Unlike Uses, this class retains the complete ReachingDefinitions object for
 * every read. Consequently, clients can distinguish full bit-range coverage
 * from a partially covered read, a read affected by an unmodelled write, or
 * a read whose function-entry value can reach it on a CFG alternative.
 * Clients performing a semantic rewrite must still establish ordering and
 * dominance for the concrete definition terms they consume.
 * It is a snapshot: all referenced IR terms must outlive this object, and the
 * graph must be rebuilt after mutating the IR or rerunning dataflow.
 */
class DefUseGraph {
public:
    /** Information about the definitions reaching one read term. */
    class DefinitionSet {
        MemoryLocation location_; ///< Location read by the term.
        ReachingDefinitions reachingDefinitions_; ///< Definitions, including unknown chunks.
        bool coversWholeLocation_; ///< Whether chunks cover the entire read location.
        bool hasUnknownDefinition_; ///< Whether an unmodelled definition reaches the read.
        bool hasIncomingDefinition_; ///< Whether a function-entry value reaches the read.
        const Term *uniqueDefinition_; ///< Sole complete definition, if one exists.

    public:
        DefinitionSet();

        DefinitionSet(const MemoryLocation &location,
                      const ReachingDefinitions &reachingDefinitions);

        const MemoryLocation &location() const { return location_; }

        const ReachingDefinitions &reachingDefinitions() const {
            return reachingDefinitions_;
        }

        /** True if reaching-definition chunks cover every bit of the read. */
        bool coversWholeLocation() const { return coversWholeLocation_; }

        /** True if an unmodelled write occurs in the reaching information. */
        bool hasUnknownDefinition() const { return hasUnknownDefinition_; }

        /** True if a CFG path supplies the value present at function entry. */
        bool hasIncomingDefinition() const {
            return hasIncomingDefinition_;
        }

        /**
         * True only when every bit is represented and no explicitly unknown
         * definition can reach the read. This does not prove that an absent
         * definition on another CFG predecessor has been represented.
         */
        bool isComplete() const {
            return coversWholeLocation_ && !hasUnknownDefinition_ &&
                !hasIncomingDefinition_;
        }

        /**
         * Returns the sole definition of the complete read, or nullptr when
         * the read is partial, unknown, or has multiple definitions.
         */
        const Term *uniqueDefinition() const { return uniqueDefinition_; }
    };

    /** A range of a read term which uses a definition. */
    class Use {
        MemoryLocation location_;
        const Term *term_;

    public:
        Use(const MemoryLocation &location, const Term *term):
            location_(location), term_(term)
        {}

        const MemoryLocation &location() const { return location_; }
        const Term *term() const { return term_; }
    };

private:
    /** Mapping from a read term to all definitions reaching it. */
    boost::unordered_map<const Term *, DefinitionSet> read2definitions_;

    /** Mapping from a write term to all ranges which use it. */
    boost::unordered_map<const Term *, std::vector<Use>> definition2uses_;

public:
    explicit DefUseGraph(const Dataflow &dataflow);

    /** Returns all reaching-definition information for a read term. */
    const DefinitionSet &definitions(const Term *read) const;

    /**
     * Returns a definition only when it is the sole known definition of every
     * bit in the read term.  Otherwise returns nullptr.
     */
    const Term *uniqueDefinition(const Term *read) const {
        return definitions(read).uniqueDefinition();
    }

    /** Returns all uses of a write term, including uses which are not unique. */
    const std::vector<Use> &uses(const Term *definition) const;
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
