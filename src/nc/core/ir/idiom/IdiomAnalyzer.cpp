/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "IdiomAnalyzer.h"

#include <climits>
#include <limits>
#include <vector>

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/CancellationToken.h>
#include <nc/common/Foreach.h>
#include <nc/common/make_unique.h>

#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/cflow/BasicNode.h>
#include <nc/core/ir/cflow/Graph.h>
#include <nc/core/ir/cflow/LoopAnalysis.h>
#include <nc/core/ir/cflow/Region.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DefUseGraph.h>
#include <nc/core/ir/dflow/ReachingDefinitions.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/dflow/ValueProvenance.h>
#include <nc/core/ir/effects/ExpressionEffects.h>
#include <nc/core/ir/liveness/Liveness.h>

#include "Idioms.h"
#include "MemoryFill.h"

namespace nc {
namespace core {
namespace ir {
namespace idiom {

namespace {

typedef boost::unordered_set<const BasicBlock *> BlockSet;
typedef boost::unordered_set<const Assignment *> AssignmentSet;

void collectBlocks(const cflow::Node *node, BlockSet &blocks) {
    assert(node != nullptr);

    if (const cflow::BasicNode *basicNode = node->as<cflow::BasicNode>()) {
        blocks.insert(basicNode->basicBlock());
    } else if (const cflow::Region *region = node->as<cflow::Region>()) {
        foreach (const cflow::Node *child, region->nodes()) {
            collectBlocks(child, blocks);
        }
    }
}

bool containsExactly(const cflow::Region *region,
                     const cflow::NaturalLoop &loop) {
    assert(region != nullptr);

    BlockSet regionBlocks;
    collectBlocks(region, regionBlocks);
    if (regionBlocks.size() != loop.blocks().size()) {
        return false;
    }
    foreach (const BasicBlock *block, loop.blocks()) {
        if (regionBlocks.find(block) == regionBlocks.end()) {
            return false;
        }
    }
    return true;
}

/** Finds only an output region; this result is not part of recognition. */
const cflow::Region *findStructuredRegion(const cflow::Node *node,
                                         const cflow::NaturalLoop &loop) {
    if (!node) {
        return nullptr;
    }

    const cflow::Region *region = node->as<cflow::Region>();
    if (!region) {
        return nullptr;
    }

    foreach (const cflow::Node *child, region->nodes()) {
        if (const cflow::Region *result = findStructuredRegion(child, loop)) {
            return result;
        }
    }

    const bool isLoopRegion = region->regionKind() == cflow::Region::WHILE ||
        region->regionKind() == cflow::Region::DO_WHILE ||
        region->regionKind() == cflow::Region::LOOP;
    return isLoopRegion && region->getEntryBasicBlock() == loop.header() &&
        containsExactly(region, loop) ? region : nullptr;
}

void collectStatements(const cflow::NaturalLoop &loop,
                       std::vector<const Statement *> &statements) {
    foreach (const BasicBlock *block, loop.blocks()) {
        foreach (const Statement *statement, block->statements()) {
            statements.push_back(statement);
        }
    }
}

bool containsDereference(const Term *term) {
    if (!term) {
        return false;
    }
    if (term->is<Dereference>()) {
        return true;
    }

    bool result = false;
    term->callOnChildren([&](const Term *child) {
        if (!result && containsDereference(child)) {
            result = true;
        }
    });
    return result;
}

bool sameLocation(const Term *left, const Term *right,
                  const dflow::Dataflow &dataflow) {
    const MemoryLocation &leftLocation = dataflow.getMemoryLocation(left);
    return leftLocation && leftLocation == dataflow.getMemoryLocation(right);
}

bool getConcreteSignedValue(const Term *term, const dflow::Dataflow &dataflow,
                            SignedConstantValue &result) {
    const dflow::Value *value = dataflow.findValue(term);
    if (!value || !value->abstractValue().isConcrete()) {
        return false;
    }
    result = value->abstractValue().asConcrete().signedValue();
    return true;
}

bool strictlyPrecedesInBlock(const Statement *first, const Statement *second);
bool isRegisterLocation(const MemoryLocation &location);
bool isSafeToEvaluateOnce(const Term *term,
                          const dflow::Dataflow &dataflow);

/**
 * Expands a pure register temporary into the exact definition which reaches
 * this read. Definitions must occur earlier in the same basic block, so a
 * loop-carried value or a value captured before the loop is never mistaken
 * for a temporary computed for the current update.
 */
const Term *expandRegisterTemporary(
        const Term *term, const MemoryLocation &updateLocation,
        const dflow::Dataflow &dataflow, const dflow::DefUseGraph &defUse,
        boost::unordered_set<const Term *> &expanding,
        AssignmentSet &dependencies, std::size_t depth) {
    assert(term != nullptr);
    assert(updateLocation);

    static const std::size_t MAX_UPDATE_EXPANSION_DEPTH = 32;
    if (depth > MAX_UPDATE_EXPANSION_DEPTH) {
        return nullptr;
    }
    if (!term->asMemoryLocationAccess() || !term->isRead()) {
        return term;
    }

    const MemoryLocation &readLocation = dataflow.getMemoryLocation(term);
    if (!isRegisterLocation(readLocation) || readLocation == updateLocation) {
        return term;
    }
    if (!expanding.insert(term).second) {
        return nullptr;
    }

    struct EraseOnReturn {
        boost::unordered_set<const Term *> &set;
        const Term *term;
        ~EraseOnReturn() { set.erase(term); }
    } eraseOnReturn{expanding, term};

    const dflow::DefUseGraph::DefinitionSet &definitions =
        defUse.definitions(term);
    const Term *definition = definitions.uniqueDefinition();
    const Statement *definitionStatement =
        definition ? definition->statement() : nullptr;
    const Assignment *definitionAssignment = definitionStatement ?
        definitionStatement->asAssignment() : nullptr;
    if (!definitions.isComplete() || definitions.location() != readLocation ||
        !definition || dataflow.getMemoryLocation(definition) != readLocation ||
        !definition->source() || !definitionAssignment ||
        definitionAssignment->left() != definition)
    {
        return nullptr;
    }
    if (!definitionStatement ||
        !strictlyPrecedesInBlock(definitionStatement, term->statement()))
    {
        /* A definition from another block is an input to this update, not an
         * instruction-local temporary to inline here. */
        return term;
    }
    if (!isSafeToEvaluateOnce(definition->source(), dataflow)) {
        return nullptr;
    }

    const Term *result = expandRegisterTemporary(
        definition->source(), updateLocation, dataflow, defUse, expanding,
        dependencies, depth + 1);
    if (result) {
        dependencies.insert(definitionAssignment);
    }
    return result;
}

/**
 * Matches x = x +/- constant after expanding pure register temporaries and
 * returns the read of x and its signed step.
 */
bool getSelfUpdate(const Assignment *assignment,
                   const dflow::Dataflow &dataflow,
                   const dflow::DefUseGraph &defUse,
                   const dflow::ValueProvenance &provenance,
                   const Term *&read,
                   SignedConstantValue &step,
                   AssignmentSet &dependencies) {
    assert(assignment != nullptr);

    const MemoryLocation &updateLocation =
        dataflow.getMemoryLocation(assignment->left());
    if (!isRegisterLocation(updateLocation) ||
        !isSafeToEvaluateOnce(assignment->right(), dataflow))
    {
        return false;
    }

    boost::unordered_set<const Term *> expanding;
    AssignmentSet candidateDependencies;
    const Term *expanded = expandRegisterTemporary(
        assignment->right(), updateLocation, dataflow, defUse, expanding,
        candidateDependencies, 0);
    const BinaryOperator *binary = expanded ? expanded->asBinaryOperator() : nullptr;
    if (!binary) {
        return false;
    }

    const Term *left = expandRegisterTemporary(
        binary->left(), updateLocation, dataflow, defUse, expanding,
        candidateDependencies, 0);
    const Term *right = expandRegisterTemporary(
        binary->right(), updateLocation, dataflow, defUse, expanding,
        candidateDependencies, 0);
    if (!left || !right) {
        return false;
    }

    const Term *amountTerm = nullptr;
    bool subtract = false;
    if (sameLocation(assignment->left(), left, dataflow)) {
        read = left;
        amountTerm = right;
        subtract = binary->operatorKind() == BinaryOperator::SUB;
        if (binary->operatorKind() != BinaryOperator::ADD && !subtract) {
            return false;
        }
    } else if (binary->operatorKind() == BinaryOperator::ADD &&
               sameLocation(assignment->left(), right, dataflow)) {
        read = right;
        amountTerm = left;
    } else {
        return false;
    }

    SignedConstantValue amount;
    if (!provenance.isPathComplete(amountTerm) ||
        !getConcreteSignedValue(amountTerm, dataflow, amount)) {
        return false;
    }
    if (subtract) {
        if (amount == (std::numeric_limits<SignedConstantValue>::min)()) {
            return false;
        }
        amount = -amount;
    }

    step = amount;
    if (step == 0) {
        return false;
    }
    candidateDependencies.insert(assignment);
    dependencies.swap(candidateDependencies);
    return true;
}

bool isSyntacticZero(const Term *term) {
    if (const Constant *constant = term->asConstant()) {
        return constant->value().value() == 0;
    }

    if (const UnaryOperator *unary = term->asUnaryOperator()) {
        if (unary->operatorKind() == UnaryOperator::ZERO_EXTEND ||
            unary->operatorKind() == UnaryOperator::SIGN_EXTEND)
        {
            return isSyntacticZero(unary->operand());
        }
    }
    return false;
}

enum CountPredicate {
    NOT_COUNT_PREDICATE,
    COUNT_IS_ZERO,
    COUNT_IS_NONZERO
};

bool strictlyPrecedesInBlock(const Statement *first, const Statement *second) {
    if (!first || !second || first == second || !first->basicBlock() ||
        first->basicBlock() != second->basicBlock())
    {
        return false;
    }

    bool sawFirst = false;
    foreach (const Statement *statement, first->basicBlock()->statements()) {
        if (statement == second) {
            return sawFirst;
        }
        sawFirst = sawFirst || statement == first;
    }
    return false;
}

/**
 * Normalizes boolean forms which are exactly count == 0 or count != 0.
 * Comparisons with any other bound deliberately do not match.
 *
 * Register reads may be expanded through exact, unique definitions computed
 * earlier in the loop header. Restricting expansion to a strict same-block
 * order is important: a definition later in the header may reach a read from
 * the previous iteration, while a definition outside the loop may merely be a
 * stale predicate captured before entry. Neither denotes the current count.
 */
CountPredicate getCountPredicateImpl(
        const Term *term, const MemoryLocation &countLocation,
        const dflow::Dataflow &dataflow, const dflow::DefUseGraph &defUse,
        const BasicBlock *header, boost::unordered_set<const Term *> &expanding,
        AssignmentSet &dependencies, std::size_t depth) {
    assert(term != nullptr);
    assert(countLocation);
    assert(header != nullptr);

    static const std::size_t MAX_PREDICATE_EXPANSION_DEPTH = 32;
    if (depth > MAX_PREDICATE_EXPANSION_DEPTH) {
        return NOT_COUNT_PREDICATE;
    }

    if (term->asMemoryLocationAccess() && term->isRead() &&
        dataflow.getMemoryLocation(term) == countLocation)
    {
        return COUNT_IS_NONZERO;
    }

    if (const UnaryOperator *unary = term->asUnaryOperator()) {
        if (unary->operatorKind() == UnaryOperator::ZERO_EXTEND ||
            unary->operatorKind() == UnaryOperator::SIGN_EXTEND)
        {
            return getCountPredicateImpl(
                unary->operand(), countLocation, dataflow, defUse, header,
                expanding, dependencies, depth + 1);
        }
        if (unary->operatorKind() == UnaryOperator::NOT && term->size() == 1) {
            const CountPredicate predicate = getCountPredicateImpl(
                unary->operand(), countLocation, dataflow, defUse, header,
                expanding, dependencies, depth + 1);
            if (predicate == COUNT_IS_ZERO) {
                return COUNT_IS_NONZERO;
            }
            if (predicate == COUNT_IS_NONZERO) {
                return COUNT_IS_ZERO;
            }
        }
        return NOT_COUNT_PREDICATE;
    }

    if (const BinaryOperator *binary = term->asBinaryOperator()) {
        if (binary->operatorKind() != BinaryOperator::EQUAL) {
            return NOT_COUNT_PREDICATE;
        }

        const Term *predicateTerm = nullptr;
        if (isSyntacticZero(binary->left())) {
            predicateTerm = binary->right();
        } else if (isSyntacticZero(binary->right())) {
            predicateTerm = binary->left();
        } else {
            return NOT_COUNT_PREDICATE;
        }

        const CountPredicate predicate = getCountPredicateImpl(
            predicateTerm, countLocation, dataflow, defUse, header,
            expanding, dependencies, depth + 1);
        if (predicate == COUNT_IS_ZERO) {
            return COUNT_IS_NONZERO;
        }
        if (predicate == COUNT_IS_NONZERO) {
            return COUNT_IS_ZERO;
        }
        return NOT_COUNT_PREDICATE;
    }

    const MemoryLocation &readLocation = dataflow.getMemoryLocation(term);
    if (!term->asMemoryLocationAccess() || !term->isRead() || !readLocation ||
        !expanding.insert(term).second)
    {
        return NOT_COUNT_PREDICATE;
    }

    struct EraseOnReturn {
        boost::unordered_set<const Term *> &set;
        const Term *term;
        ~EraseOnReturn() { set.erase(term); }
    } eraseOnReturn{expanding, term};

    const dflow::DefUseGraph::DefinitionSet &definitions =
        defUse.definitions(term);
    const Term *definition = definitions.uniqueDefinition();
    const Statement *definitionStatement =
        definition ? definition->statement() : nullptr;
    const Assignment *definitionAssignment = definitionStatement ?
        definitionStatement->asAssignment() : nullptr;
    if (!definitions.isComplete() || definitions.location() != readLocation ||
        !definition || dataflow.getMemoryLocation(definition) != readLocation ||
        !definition->source() || !definitionAssignment ||
        definitionAssignment->left() != definition ||
        definitionStatement->basicBlock() != header ||
        !strictlyPrecedesInBlock(definitionStatement, term->statement()))
    {
        return NOT_COUNT_PREDICATE;
    }

    const CountPredicate result = getCountPredicateImpl(
        definition->source(), countLocation, dataflow, defUse, header,
        expanding, dependencies, depth + 1);
    if (result != NOT_COUNT_PREDICATE) {
        dependencies.insert(definitionAssignment);
    }
    return result;
}

CountPredicate getCountPredicate(
        const Term *term, const MemoryLocation &countLocation,
        const dflow::Dataflow &dataflow, const dflow::DefUseGraph &defUse,
        const BasicBlock *header, AssignmentSet &dependencies) {
    boost::unordered_set<const Term *> expanding;
    AssignmentSet candidateDependencies;
    const CountPredicate result = getCountPredicateImpl(
        term, countLocation, dataflow, defUse, header, expanding,
        candidateDependencies, 0);
    if (result != NOT_COUNT_PREDICATE) {
        dependencies.swap(candidateDependencies);
    }
    return result;
}

const Term *getUniqueLoopEntryDefinition(
        const Term *read, const Term *loopDefinition,
        const cflow::NaturalLoop &loop, const dflow::Dataflow &dataflow,
        const dflow::DefUseGraph &defUse,
        const Dominators &dominators) {
    if (!read || !read->isRead() || !loopDefinition ||
        !loopDefinition->isWrite())
    {
        return nullptr;
    }

    /* A dedicated preheader is the dynamic execution proof: every external
     * entry into the loop passes through this block, while back edges do not.
     * A merely dominating function-entry definition is insufficient for an
     * inner loop that is entered repeatedly by an outer loop. */
    const BasicBlock *preheader = loop.preheader();
    if (!preheader) {
        return nullptr;
    }

    const dflow::DefUseGraph::DefinitionSet &definitions =
        defUse.definitions(read);
    const MemoryLocation &readLocation = dataflow.getMemoryLocation(read);
    if (!readLocation || !definitions.isComplete() ||
        dataflow.getMemoryLocation(loopDefinition) != readLocation)
    {
        return nullptr;
    }

    bool sawLoopDefinition = false;
    const Term *result = nullptr;
    foreach (const dflow::ReachingDefinitions::Chunk &chunk,
             definitions.reachingDefinitions().chunks()) {
        foreach (const Term *definition, chunk.definitions()) {
            /* Do not silently reinterpret a partial/wider register write as
             * the captured induction value. */
            if (dataflow.getMemoryLocation(definition) != readLocation) {
                return nullptr;
            }
            const Statement *statement = definition->statement();
            if (statement && statement->basicBlock() &&
                loop.contains(statement->basicBlock()))
            {
                if (definition != loopDefinition) {
                    return nullptr;
                }
                sawLoopDefinition = true;
                continue;
            }

            /* Keep the captured variable definition, not its RHS. Reusing the
             * RHS at the loop site could re-read changed memory or duplicate
             * an evaluation that happened in the preheader. */
            if (!definition->source() || (result && result != definition))
            {
                return nullptr;
            }
            result = definition;
        }
    }
    if (!sawLoopDefinition || !result) {
        return nullptr;
    }

    /* ReachingDefinitions historically treats an absent definition on one
     * predecessor as the merge identity. A branch-local initializer can
     * therefore look unique even though another path reaches the loop with an
     * uninitialized value. Dominance is the path-coverage proof required by
     * this semantic rewrite. */
    const Statement *statement = result->statement();
    if (!statement || !statement->basicBlock() ||
        loop.contains(statement->basicBlock()) ||
        statement->basicBlock() != preheader ||
        !dominators.isDominating(statement->basicBlock(), loop.header()))
    {
        return nullptr;
    }
    return result;
}

/**
 * True when evaluating a term once cannot trap or perform an observable
 * memory operation. This is deliberately stricter than loop invariance:
 * replacing a loop also changes zero evaluations into one evaluation when
 * the original trip count is zero.
 */
bool isRegisterLocation(const MemoryLocation &location) {
    return location &&
        location.domain() >= MemoryDomain::FIRST_REGISTER &&
        location.domain() <= MemoryDomain::LAST_REGISTER;
}

bool isSafeToEvaluateOnce(const Term *term,
                          const dflow::Dataflow &dataflow) {
    assert(term != nullptr);
    return effects::ExpressionEffects::analyze(term, dataflow)
        .canEvaluateSpeculatively();
}

/**
 * True when discarding evaluation of a dead scalar expression cannot remove
 * an observable read or a possible trap. Intrinsics describe value quality,
 * not an operation, so UNKNOWN and UNDEFINED flag values are safe to discard.
 * This predicate must not be used for expressions which are hoisted or
 * evaluated by the replacement operation.
 */
bool isSafeToDiscard(const Term *term,
                     const dflow::Dataflow &dataflow) {
    assert(term != nullptr);
    return effects::ExpressionEffects::analyze(term, dataflow).canDiscard();
}

bool isLoopInvariant(const Term *term, const cflow::NaturalLoop &loop,
                     const dflow::Dataflow &dataflow,
                     const dflow::DefUseGraph &defUse,
                     const Dominators &dominators) {
    assert(term != nullptr);

    if (term->is<Dereference>()) {
        return false;
    }

    if (term->asMemoryLocationAccess() && term->isRead()) {
        const MemoryLocation &location = dataflow.getMemoryLocation(term);
        if (!location) {
            return false;
        }

        const dflow::DefUseGraph::DefinitionSet &definitions =
            defUse.definitions(term);
        const Term *definition = definitions.uniqueDefinition();
        const Statement *statement = definition ? definition->statement() : nullptr;
        if (!definitions.isComplete() || !definition || !statement ||
            !statement->basicBlock() ||
            loop.contains(statement->basicBlock()) ||
            !dominators.isDominating(statement->basicBlock(), loop.header()))
        {
            return false;
        }
    }

    bool result = true;
    term->callOnChildren([&](const Term *child) {
        if (result && !isLoopInvariant(
                child, loop, dataflow, defUse, dominators)) {
            result = false;
        }
    });
    return result;
}

bool hasExternalLiveUse(const Term *write,
                        const dflow::DefUseGraph &defUse,
                        const liveness::Liveness &liveness,
                        const cflow::NaturalLoop &loop) {
    assert(write != nullptr && write->isWrite());

    foreach (const dflow::DefUseGraph::Use &use, defUse.uses(write)) {
        if (!liveness.isLive(use.term())) {
            continue;
        }
        const Statement *statement = use.term()->statement();
        if (!statement || !statement->basicBlock() ||
            !loop.contains(statement->basicBlock()))
        {
            return true;
        }
    }
    return false;
}

bool executesBefore(const Statement *first, const Statement *second,
                    const Dominators &dominators) {
    assert(first != nullptr && second != nullptr);
    assert(first->basicBlock() != nullptr && second->basicBlock() != nullptr);

    if (first->basicBlock() != second->basicBlock()) {
        return dominators.isDominating(first->basicBlock(),
                                       second->basicBlock());
    }

    foreach (const Statement *statement, first->basicBlock()->statements()) {
        if (statement == first) {
            return true;
        }
        if (statement == second) {
            return false;
        }
    }
    return false;
}

struct PreTestLoopShape {
    const Jump *headerJump;
    const BasicBlock *bodyEntry;
    const BasicBlock *exit;
    const BasicBlock *latch;
    bool bodyOnTrue;
};

bool isResolvedSingleTarget(const JumpTarget &target) {
    if (!target.basicBlock() || target.table()) {
        return false;
    }

    /* IR generation deliberately retains the address expression after it
     * resolves an ordinary direct branch to a BasicBlock.  Its presence does
     * not make the edge indirect.  When an expression is retained, however,
     * verify that it is a pure, concrete expression for this exact block so a
     * loop summary cannot hide an unresolved or observable target lookup. */
    if (!target.address()) {
        return true;
    }
    if (!target.basicBlock()->address() ||
        *target.basicBlock()->address() < 0)
    {
        return false;
    }

    /* A cached concrete value is insufficient here: until every value leaf
     * has a path-complete provenance proof, a predecessor with no definition
     * can disappear from the legacy reaching-definition merge.  Canonical
     * direct control-flow edges retain their literal target, so require that
     * representation and reject computed targets conservatively. */
    const Constant *address = target.address()->asConstant();
    return address && address->value().value() ==
            static_cast<ConstantValue>(*target.basicBlock()->address());
}

bool hasOnlyResolvedSingleTargetJumps(const cflow::NaturalLoop &loop) {
    foreach (const BasicBlock *block, loop.blocks()) {
        const Jump *jump = block->getJump();
        if (!jump || !isResolvedSingleTarget(jump->thenTarget())) {
            return false;
        }
        if (jump->isConditional()) {
            if (!isResolvedSingleTarget(jump->elseTarget())) {
                return false;
            }
        } else if (jump->elseTarget().basicBlock() ||
                   jump->elseTarget().address() ||
                   jump->elseTarget().table())
        {
            return false;
        }
    }
    return true;
}

/** Returns whether the loop body remains cyclic after removing its one
 * canonical latch-to-header edge. */
bool hasAdditionalCycle(const cflow::NaturalLoop &loop, const CFG &cfg,
                        const BasicBlock *latch,
                        const CancellationToken &canceled) {
    /* Kahn's algorithm avoids recursion on adversarially deep CFGs.  Once the
     * canonical back edge is removed, any nodes left with positive indegree
     * belong to an additional cycle which the semantic summary cannot hide. */
    boost::unordered_map<const BasicBlock *, std::size_t> indegree;
    foreach (const BasicBlock *block, loop.blocks()) {
        indegree[block] = 0;
    }
    foreach (const BasicBlock *block, loop.blocks()) {
        foreach (const BasicBlock *successor, cfg.getSuccessors(block)) {
            if (loop.contains(successor) &&
                !(block == latch && successor == loop.header()))
            {
                ++indegree[successor];
            }
        }
        canceled.poll();
    }

    std::vector<const BasicBlock *> worklist;
    foreach (const BasicBlock *block, loop.blocks()) {
        if (indegree[block] == 0) {
            worklist.push_back(block);
        }
    }

    std::size_t removed = 0;
    while (!worklist.empty()) {
        const BasicBlock *block = worklist.back();
        worklist.pop_back();
        ++removed;
        foreach (const BasicBlock *successor, cfg.getSuccessors(block)) {
            if (!loop.contains(successor) ||
                (block == latch && successor == loop.header()))
            {
                continue;
            }
            assert(indegree[successor] > 0);
            if (--indegree[successor] == 0) {
                worklist.push_back(successor);
            }
        }
        canceled.poll();
    }
    return removed != loop.blocks().size();
}

bool getPreTestLoopShape(const cflow::NaturalLoop &loop, const CFG &cfg,
                         const CancellationToken &canceled,
                         PreTestLoopShape &result) {
    const BasicBlock *header = loop.header();
    if (!header || loop.blocks().size() < 2 || loop.latches().size() != 1 ||
        loop.exits().size() != 1 ||
        !hasOnlyResolvedSingleTargetJumps(loop))
    {
        return false;
    }

    const Jump *headerJump = header->getJump();
    if (!headerJump || !headerJump->isConditional()) {
        return false;
    }
    const BasicBlock *thenTarget = headerJump->thenTarget().basicBlock();
    const BasicBlock *elseTarget = headerJump->elseTarget().basicBlock();
    if (!thenTarget || !elseTarget) {
        return false;
    }
    const bool thenIsBody = loop.contains(thenTarget);
    const bool elseIsBody = loop.contains(elseTarget);
    if (thenIsBody == elseIsBody) {
        return false;
    }
    const BasicBlock *bodyEntry = thenIsBody ? thenTarget : elseTarget;
    const BasicBlock *exit = thenIsBody ? elseTarget : thenTarget;
    if (bodyEntry == header)
    {
        return false;
    }
    if (loop.exits().front().source() != header ||
        loop.exits().front().target() != exit)
    {
        return false;
    }

    const BasicBlock *latch = loop.latches().front();
    if (hasAdditionalCycle(loop, cfg, latch, canceled)) {
        /* Each body statement must execute at most once between two header
         * tests. This also rejects irreducible internal SCCs whose edges are
         * not individually dominance-classified as natural back edges. */
        return false;
    }

    result.headerJump = headerJump;
    result.bodyEntry = bodyEntry;
    result.exit = exit;
    result.latch = latch;
    result.bodyOnTrue = thenIsBody;
    return true;
}

} // anonymous namespace

IdiomAnalyzer::IdiomAnalyzer(FunctionIdioms &result, const Function *function,
        const cflow::Graph &graph, const dflow::Dataflow &dataflow,
        const liveness::Liveness &liveness,
        const CancellationToken &canceled):
    result_(result), function_(function), graph_(graph), dataflow_(dataflow),
    liveness_(liveness), canceled_(canceled)
{
    assert(function_ != nullptr);
}

void IdiomAnalyzer::analyze() {
    if (!function_->entry() || function_->basicBlocks().empty() ||
        !dataflow_.converged())
    {
        return;
    }


    /* Inline assembly currently has no explicit read/write/clobber model in
     * DataflowAnalyzer.  Until it does, no whole-loop semantic replacement in
     * the containing function can rely on the apparent reaching definitions. */
    foreach (const BasicBlock *block, function_->basicBlocks()) {
        foreach (const Statement *statement, block->statements()) {
            if (statement->kind() == Statement::INLINE_ASSEMBLY) {
                return;
            }
        }
    }

    /*
     * These analysis views retain pointers into immutable IR.  Idiom recovery
     * must therefore run after IR/dataflow stabilization and before any pass
     * which mutates the function.
     */
    CFG cfg(function_->basicBlocks());
    Dominators dominators(cfg, canceled_, function_->entry());
    cflow::LoopAnalysis loopAnalysis(cfg, dominators, function_->entry());
    dflow::DefUseGraph defUse(dataflow_);
    dflow::ValueProvenance provenance(dataflow_, defUse, dominators, cfg);

    foreach (const cflow::NaturalLoop &loop, loopAnalysis.loops()) {
        canceled_.poll();
        const cflow::Region *region = findStructuredRegion(graph_.root(), loop);
        if (std::unique_ptr<MemoryFill> memoryFill = recognizeMemoryFill(
                loop, region, cfg, dominators, defUse, provenance))
        {
            result_.addMemoryFill(std::move(memoryFill));
        }
    }
}

std::unique_ptr<MemoryFill> IdiomAnalyzer::recognizeMemoryFill(
        const cflow::NaturalLoop &loop, const cflow::Region *region,
        const CFG &cfg, const Dominators &dominators,
        const dflow::DefUseGraph &defUse,
        const dflow::ValueProvenance &provenance) const {
    /* Only a canonical pre-test loop is summarized at this stage. */
    PreTestLoopShape shape;
    if (!getPreTestLoopShape(loop, cfg, canceled_, shape)) {
        return nullptr;
    }
    if (region && region->exitBasicBlock() != shape.exit) {
        /* Code generation continues from the structured region's exit.  Do
         * not attach a summary when that structural view disagrees with the
         * independently proved CFG exit. */
        return nullptr;
    }
    const BasicBlock *header = loop.header();
    const Jump *headerJump = shape.headerJump;
    const BasicBlock *latch = shape.latch;

    std::vector<const Statement *> statements;
    collectStatements(loop, statements);
    if (statements.empty()) {
        return nullptr;
    }

    const Assignment *memoryWrite = nullptr;
    std::vector<const Assignment *> scalarAssignments;
    std::vector<const Jump *> conditionalJumps;

    foreach (const Statement *statement, statements) {
        if (const Assignment *assignment = statement->asAssignment()) {
            const Dereference *destination = assignment->left()->asDereference();
            if (destination) {
                if (memoryWrite || destination->domain() != MemoryDomain::MEMORY ||
                    containsDereference(assignment->right()))
                {
                    return nullptr;
                }
                memoryWrite = assignment;
            } else {
                /* Scalar bookkeeping must not hide any other memory effect. */
                if (containsDereference(assignment->left()) ||
                    containsDereference(assignment->right()))
                {
                    return nullptr;
                }
                scalarAssignments.push_back(assignment);
            }
        } else if (const Jump *jump = statement->asJump()) {
            if (jump->isConditional()) {
                conditionalJumps.push_back(jump);
            }
        } else if (statement->kind() != Statement::CALLBACK &&
                   statement->kind() != Statement::REMEMBER_REACHING_DEFINITIONS)
        {
            /* Calls, touches, invalidations, and assembly are memory barriers. */
            return nullptr;
        }
    }

    if (!memoryWrite || memoryWrite->basicBlock() == header ||
        conditionalJumps.size() != 1 || conditionalJumps.front() != headerJump)
    {
        return nullptr;
    }

    const Dereference *destinationDereference =
        memoryWrite->left()->asDereference();
    if (!destinationDereference || destinationDereference->size() <= 0 ||
        destinationDereference->size() % CHAR_BIT != 0)
    {
        return nullptr;
    }
    const SignedConstantValue elementBytes =
        destinationDereference->size() / CHAR_BIT;

    struct Update {
        const Assignment *assignment;
        const Term *read;
        SignedConstantValue step;
        AssignmentSet dependencies;
    };
    std::vector<Update> updates;
    foreach (const Assignment *assignment, scalarAssignments) {
        const Term *read = nullptr;
        SignedConstantValue step = 0;
        AssignmentSet dependencies;
        if (getSelfUpdate(assignment, dataflow_, defUse, provenance,
                          read, step,
                          dependencies))
        {
            updates.push_back(
                Update{assignment, read, step, std::move(dependencies)});
        }
    }

    const Assignment *destinationUpdate = nullptr;
    const Term *destinationRead = nullptr;
    AssignmentSet consumedAssignments;
    foreach (const Update &update, updates) {
        if (sameLocation(destinationDereference->address(), update.read,
                         dataflow_) && update.step == elementBytes)
        {
            if (destinationUpdate) {
                return nullptr;
            }
            destinationUpdate = update.assignment;
            destinationRead = update.read;
            consumedAssignments.insert(update.dependencies.begin(),
                                       update.dependencies.end());
        }
    }
    if (!destinationUpdate || !destinationRead ||
        destinationUpdate->basicBlock() == header ||
        destinationDereference->address()->size() != destinationRead->size() ||
        destinationUpdate->left()->size() != destinationRead->size())
    {
        return nullptr;
    }

    const Assignment *countUpdate = nullptr;
    const Term *countRead = nullptr;
    AssignmentSet countDependencies;
    foreach (const Update &update, updates) {
        if (update.assignment == destinationUpdate || update.step != -1) {
            continue;
        }

        const MemoryLocation &location =
            dataflow_.getMemoryLocation(update.assignment->left());
        AssignmentSet predicateDependencies;
        const CountPredicate predicate = location ?
            getCountPredicate(headerJump->condition(), location, dataflow_,
                              defUse, header, predicateDependencies) :
            NOT_COUNT_PREDICATE;
        const bool continuesWhileNonzero =
            (shape.bodyOnTrue && predicate == COUNT_IS_NONZERO) ||
            (!shape.bodyOnTrue && predicate == COUNT_IS_ZERO);
        if (continuesWhileNonzero)
        {
            if (countUpdate) {
                return nullptr;
            }
            countUpdate = update.assignment;
            countRead = update.read;
            countDependencies = update.dependencies;
            countDependencies.insert(predicateDependencies.begin(),
                                     predicateDependencies.end());
        }
    }
    if (!countUpdate || !countRead || countUpdate->basicBlock() == header ||
        sameLocation(countRead, destinationRead, dataflow_))
    {
        return nullptr;
    }
    consumedAssignments.insert(countDependencies.begin(),
                               countDependencies.end());

    const MemoryLocation &destinationLocation =
        dataflow_.getMemoryLocation(destinationUpdate->left());
    const MemoryLocation &countLocation =
        dataflow_.getMemoryLocation(countUpdate->left());
    if (!isRegisterLocation(destinationLocation) ||
        !isRegisterLocation(countLocation))
    {
        return nullptr;
    }
    foreach (const Assignment *assignment, scalarAssignments) {
        const MemoryLocation &location =
            dataflow_.getMemoryLocation(assignment->left());
        if (!isRegisterLocation(location) ||
            !isSafeToDiscard(assignment->right(), dataflow_))
        {
            return nullptr;
        }
        if (liveness_.isLive(assignment->left()) &&
            consumedAssignments.find(assignment) == consumedAssignments.end())
        {
            /* A live scalar dependency which was not proved to be part of
             * either recurrence or the normalized loop predicate may affect
             * a semantic root we have not modeled. */
            return nullptr;
        }
        if ((location.overlaps(destinationLocation) &&
             assignment != destinationUpdate) ||
            (location.overlaps(countLocation) && assignment != countUpdate))
        {
            return nullptr;
        }
    }

    /* The store and both induction updates must execute on every iteration. */
    if (!dominators.isDominating(memoryWrite->basicBlock(), latch) ||
        !dominators.isDominating(destinationUpdate->basicBlock(), latch) ||
        !dominators.isDominating(countUpdate->basicBlock(), latch) ||
        !executesBefore(memoryWrite, destinationUpdate, dominators))
    {
        return nullptr;
    }

    const Term *initialDestination = getUniqueLoopEntryDefinition(
        destinationRead, destinationUpdate->left(), loop, dataflow_, defUse,
        dominators);
    const Term *initialCount = getUniqueLoopEntryDefinition(
        countRead, countUpdate->left(), loop, dataflow_, defUse,
        dominators);
    if (!initialDestination || !initialCount ||
        initialDestination->size() != destinationRead->size() ||
        initialCount->size() != countRead->size() ||
        !provenance.isUnclobberedBetween(initialDestination,
                                         destinationRead) ||
        !provenance.isUnclobberedBetween(initialCount, countRead) ||
        !provenance.isPathComplete(initialDestination) ||
        !provenance.isPathComplete(initialCount) ||
        !provenance.isPathComplete(memoryWrite->right()) ||
        !isLoopInvariant(memoryWrite->right(), loop, dataflow_, defUse,
                         dominators) ||
        !isSafeToEvaluateOnce(memoryWrite->right(), dataflow_))
    {
        return nullptr;
    }

    foreach (const Assignment *assignment, scalarAssignments) {
        if (hasExternalLiveUse(assignment->left(), defUse, liveness_, loop)) {
            return nullptr;
        }
    }

    return std::make_unique<MemoryFill>(
        header, region, initialDestination, memoryWrite->right(), initialCount,
        destinationDereference->address()->size(),
        destinationDereference->size(), elementBytes, memoryWrite,
        std::move(statements));
}

} // namespace idiom
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
