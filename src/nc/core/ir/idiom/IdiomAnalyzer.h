/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <memory>

namespace nc {

class CancellationToken;

namespace core {
namespace ir {

class Function;
class CFG;
class Dominators;

namespace cflow {
    class Graph;
    class NaturalLoop;
    class Region;
}

namespace dflow {
    class Dataflow;
    class DefUseGraph;
    class ValueProvenance;
}

namespace liveness {
    class Liveness;
}

namespace idiom {

class FunctionIdioms;
class MemoryFill;

/**
 * Recovers architecture-neutral semantic operations from IR.
 *
 * Recognition is proved from natural loops, def-use information, memory
 * effects, and induction updates.  Structured regions are used only to map a
 * proven operation to code-generation output.  Instruction spelling and
 * source-level library names are intentionally outside this layer.
 */
class IdiomAnalyzer {
    FunctionIdioms &result_;
    const Function *function_;
    const cflow::Graph &graph_;
    const dflow::Dataflow &dataflow_;
    const liveness::Liveness &liveness_;
    const CancellationToken &canceled_;

public:
    IdiomAnalyzer(FunctionIdioms &result, const Function *function,
                  const cflow::Graph &graph, const dflow::Dataflow &dataflow,
                  const liveness::Liveness &liveness,
                  const CancellationToken &canceled);

    void analyze();

private:
    std::unique_ptr<MemoryFill> recognizeMemoryFill(
        const cflow::NaturalLoop &loop, const cflow::Region *region,
        const CFG &cfg, const Dominators &dominators,
        const dflow::DefUseGraph &defUse,
        const dflow::ValueProvenance &provenance) const;
};

} // namespace idiom
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
