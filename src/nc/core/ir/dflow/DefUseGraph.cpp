/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "DefUseGraph.h"

#include <cassert>

#include <nc/common/Foreach.h>
#include <nc/common/Range.h>
#include <nc/core/ir/Term.h>

#include "Dataflow.h"

namespace nc {
namespace core {
namespace ir {
namespace dflow {

DefUseGraph::DefinitionSet::DefinitionSet():
    coversWholeLocation_(false),
    hasUnknownDefinition_(false),
    hasIncomingDefinition_(false),
    uniqueDefinition_(nullptr)
{}

DefUseGraph::DefinitionSet::DefinitionSet(
        const MemoryLocation &location,
        const ReachingDefinitions &reachingDefinitions):
    location_(location),
    reachingDefinitions_(reachingDefinitions),
    coversWholeLocation_(false),
    hasUnknownDefinition_(false),
    hasIncomingDefinition_(false),
    uniqueDefinition_(nullptr)
{
    foreach (const auto &chunk, reachingDefinitions_.chunks()) {
        hasUnknownDefinition_ =
            hasUnknownDefinition_ || chunk.hasUnknownDefinition();
        hasIncomingDefinition_ =
            hasIncomingDefinition_ || chunk.hasIncomingDefinition();
    }

    if (!location_) {
        return;
    }

    BitAddr coveredUntil = location_.addr();
    const Term *candidate = nullptr;
    bool hasMultipleDefinitions = false;

    foreach (const auto &chunk, reachingDefinitions_.chunks()) {
        /* Dataflow stores a projection of the read location here. */
        assert(location_.covers(chunk.location()));

        if (chunk.location().addr() > coveredUntil) {
            /* Preserve the gap as partial coverage. */
            hasMultipleDefinitions = true;
        } else if (chunk.location().endAddr() > coveredUntil) {
            coveredUntil = chunk.location().endAddr();
        }

        foreach (const Term *definition, chunk.definitions()) {
            if (candidate == nullptr) {
                candidate = definition;
            } else if (candidate != definition) {
                hasMultipleDefinitions = true;
            }
        }
    }

    coversWholeLocation_ = coveredUntil >= location_.endAddr();
    if (isComplete() && !hasMultipleDefinitions) {
        uniqueDefinition_ = candidate;
    }
}

DefUseGraph::DefUseGraph(const Dataflow &dataflow) {
    foreach (const auto &termAndDefinitions, dataflow.term2definitions()) {
        const Term *read = termAndDefinitions.first;
        assert(read != nullptr);
        assert(read->isRead());

        read2definitions_.emplace(
            read,
            DefinitionSet(dataflow.getMemoryLocation(read),
                          termAndDefinitions.second));

        foreach (const auto &chunk, termAndDefinitions.second.chunks()) {
            foreach (const Term *definition, chunk.definitions()) {
                definition2uses_[definition].push_back(
                    Use(chunk.location(), read));
            }
        }
    }
}

const DefUseGraph::DefinitionSet &DefUseGraph::definitions(
        const Term *read) const {
    assert(read != nullptr);
    assert(read->isRead());
    return nc::find(read2definitions_, read);
}

const std::vector<DefUseGraph::Use> &DefUseGraph::uses(
        const Term *definition) const {
    assert(definition != nullptr);
    assert(definition->isWrite());
    return nc::find(definition2uses_, definition);
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
