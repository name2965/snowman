/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "ValueProvenance.h"

#include <algorithm>
#include <deque>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include <nc/common/Foreach.h>

#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Statement.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>

#include "Dataflow.h"
#include "DefUseGraph.h"

namespace nc {
namespace core {
namespace ir {
namespace dflow {

namespace {

bool isRegisterLocation(const MemoryLocation &location) {
    return location &&
        location.domain() >= MemoryDomain::FIRST_REGISTER &&
        location.domain() <= MemoryDomain::LAST_REGISTER;
}

bool isTrackedScalarLocation(const Term *term,
                             const MemoryLocation &location) {
    if (isRegisterLocation(location)) {
        return true;
    }
    /* A resolved stack access denotes a scalar object in the current frame.
     * Exact reaching definitions below still have to prove initialization
     * and stability.  Other memory domains remain potentially volatile or
     * externally mutable. */
    return location && location.domain() == MemoryDomain::STACK &&
        (term->is<MemoryLocationAccess>() || term->is<Dereference>());
}

} // anonymous namespace

bool ValueProvenance::isUnclobberedBetween(
        const Term *definition, const Term *use) const {
    if (!definition || !definition->isWrite() || !use || !use->isRead() ||
        !definition->statement() || !use->statement())
    {
        return false;
    }
    return !hasOpaqueClobberBetween(definition->statement(),
                                    use->statement());
}

bool ValueProvenance::hasOpaqueClobberBetween(
        const Statement *definition, const Statement *use) const {
    if (!definition || !use || !definition->basicBlock() ||
        !use->basicBlock())
    {
        return true;
    }

    typedef std::vector<const Statement *> Statements;
    std::map<const BasicBlock *, Statements> statements;
    foreach (const BasicBlock *block, cfg_.basicBlocks()) {
        Statements &sequence = statements[block];
        foreach (const Statement *statement, block->statements()) {
            sequence.push_back(statement);
        }
    }

    const auto definitionBlock = statements.find(definition->basicBlock());
    const auto useBlock = statements.find(use->basicBlock());
    if (definitionBlock == statements.end() || useBlock == statements.end()) {
        return true;
    }

    const Statements &definitionStatements = definitionBlock->second;
    const auto definitionPosition = std::find(
        definitionStatements.begin(), definitionStatements.end(), definition);
    if (definitionPosition == definitionStatements.end()) {
        /* Hook-local statements do not have a stable position in the
         * function CFG, so they cannot support this path proof. */
        return true;
    }

    struct State {
        const BasicBlock *block;
        std::size_t position;
        bool sawClobber;
    };

    std::deque<State> worklist;
    std::map<const BasicBlock *,
             std::set<std::pair<std::size_t, bool>>> visited;
    worklist.push_back(State{
        definition->basicBlock(),
        static_cast<std::size_t>(
            definitionPosition - definitionStatements.begin() + 1),
        false});

    while (!worklist.empty()) {
        const State state = worklist.front();
        worklist.pop_front();

        if (!visited[state.block].insert(
                std::make_pair(state.position, state.sawClobber)).second)
        {
            continue;
        }

        const auto blockStatements = statements.find(state.block);
        if (blockStatements == statements.end()) {
            return true;
        }
        const Statements &sequence = blockStatements->second;
        if (state.position < sequence.size()) {
            const Statement *statement = sequence[state.position];
            if (statement == use) {
                if (state.sawClobber) {
                    return true;
                }
                /* Continue after a clean occurrence.  A CFG cycle can reach
                 * this same static use again after a clobber but without
                 * re-executing the definition. */
            }

            bool sawClobber = state.sawClobber;
            if (statement == definition) {
                /* A loop may execute the same definition again.  Calls that
                 * occurred before the latest definition no longer matter. */
                sawClobber = false;
            } else if (statement->kind() == Statement::CALL ||
                       statement->kind() == Statement::INLINE_ASSEMBLY)
            {
                sawClobber = true;
            }
            worklist.push_back(
                State{state.block, state.position + 1, sawClobber});
            continue;
        }

        foreach (const BasicBlock *successor,
                 cfg_.getSuccessors(state.block)) {
            if (statements.find(successor) != statements.end()) {
                worklist.push_back(State{successor, 0, state.sawClobber});
            }
        }
    }

    return false;
}

bool ValueProvenance::definitionPrecedesUse(
        const Statement *definition, const Statement *use) const {
    if (!definition || !use || !definition->basicBlock() ||
        !use->basicBlock())
    {
        return false;
    }

    if (definition->basicBlock() != use->basicBlock()) {
        return dominators_.isDominating(definition->basicBlock(),
                                        use->basicBlock());
    }

    bool sawDefinition = false;
    foreach (const Statement *statement,
             definition->basicBlock()->statements()) {
        if (statement == use) {
            return sawDefinition;
        }
        sawDefinition = sawDefinition || statement == definition;
    }
    return false;
}

bool ValueProvenance::isPathComplete(const Term *term) const {
    if (!term) {
        return false;
    }

    boost::unordered_set<const Term *> visiting;
    return isPathCompleteImpl(term, visiting, 0);
}

bool ValueProvenance::isPathCompleteImpl(
        const Term *term, boost::unordered_set<const Term *> &visiting,
        std::size_t depth) const {
    static const std::size_t MAX_PROVENANCE_DEPTH = 64;
    if (!term || !term->statement() || depth > MAX_PROVENANCE_DEPTH ||
        !visiting.insert(term).second)
    {
        return false;
    }

    struct EraseOnReturn {
        boost::unordered_set<const Term *> &set;
        const Term *term;
        ~EraseOnReturn() { set.erase(term); }
    } eraseOnReturn{visiting, term};

    /* A write denotes the value assigned to it.  Limit this convenience to a
     * real assignment LHS rather than treating arbitrary writes/touches as
     * definitions with a value. */
    if (term->isWrite()) {
        const Statement *statement = term->statement();
        const Assignment *assignment = statement ?
            statement->asAssignment() : nullptr;
        return assignment && assignment->left() == term && term->source() &&
            isPathCompleteImpl(term->source(), visiting, depth + 1);
    }

    switch (term->kind()) {
        case Term::INT_CONST:
            return true;

        case Term::INTRINSIC:
            /* UNKNOWN is an explicit nondeterministic input, rather than a
             * definition missing from one path. UNDEFINED has no source-level
             * value which a semantic replacement may safely evaluate. */
            return term->asIntrinsic()->intrinsicKind() !=
                Intrinsic::UNDEFINED;

        case Term::DEREFERENCE: /* FALLTHROUGH */
        case Term::MEMORY_LOCATION_ACCESS: {
            if (!term->isRead() || !term->statement()) {
                return false;
            }

            const MemoryLocation &readLocation =
                dataflow_.getMemoryLocation(term);
            if (!isTrackedScalarLocation(term, readLocation)) {
                return false;
            }

            const DefUseGraph::DefinitionSet &definitions =
                defUse_.definitions(term);
            const Term *definition = definitions.uniqueDefinition();
            const Statement *definitionStatement = definition ?
                definition->statement() : nullptr;
            const Assignment *assignment = definitionStatement ?
                definitionStatement->asAssignment() : nullptr;
            if (!definitions.isComplete() ||
                definitions.location() != readLocation || !definition ||
                dataflow_.getMemoryLocation(definition) != readLocation ||
                !assignment || assignment->left() != definition ||
                !definition->source() ||
                !definitionPrecedesUse(definitionStatement,
                                       term->statement()) ||
                hasOpaqueClobberBetween(definitionStatement,
                                        term->statement()))
            {
                return false;
            }

            return isPathCompleteImpl(
                definition->source(), visiting, depth + 1);
        }

        case Term::UNARY_OPERATOR:
            return isPathCompleteImpl(
                term->asUnaryOperator()->operand(), visiting, depth + 1);

        case Term::BINARY_OPERATOR: {
            const BinaryOperator *binary = term->asBinaryOperator();
            return isPathCompleteImpl(
                       binary->left(), visiting, depth + 1) &&
                   isPathCompleteImpl(
                       binary->right(), visiting, depth + 1);
        }
    }

    return false;
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
