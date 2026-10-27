/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

//
// SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
// Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
// Alexander Fokin, Sergey Levin, Leonid Tsvetkov
//
// This file is part of SmartDec decompiler.
//
// SmartDec decompiler is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// SmartDec decompiler is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
//

#include "StructureAnalyzer.h"

#include <algorithm>
#include <deque>
#include <queue>
#include <set>

#include <boost/unordered_map.hpp>

#include <nc/common/Foreach.h>
#include <nc/common/Range.h>
#include <nc/common/make_unique.h>

#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/PostDominators.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DefUseGraph.h>
#include <nc/core/ir/dflow/ExpressionIdentity.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/dflow/ValueProvenance.h>
#include <nc/core/ir/effects/ExpressionEffects.h>
#include <nc/core/ir/misc/ArrayAccess.h>
#include <nc/core/ir/misc/BoundsCheck.h>
#include <nc/core/ir/misc/PatternRecognition.h>

#include "BasicNode.h"
#include "Dfs.h"
#include "Edge.h"
#include "Graph.h"
#include "LoopExplorer.h"
#include "Switch.h"

namespace nc {
namespace core {
namespace ir {
namespace cflow {

void StructureAnalyzer::analyze() {
    analyze(graph_.root());
}

void StructureAnalyzer::analyze(Region *region) {
    bool changed;

    do {
        changed = false;

        /*
         * Classify edges, sort nodes topologically.
         */
        Dfs dfs(region);

        /* Recover comparison-dispatched switches before generic if/condition
         * reductions hide the individual equality nodes.  Preorder is
         * intentional: it finds the maximal chain from its first test rather
         * than prematurely reducing a suffix. */
        foreach (Node *node, dfs.preordering()) {
            if (reduceComparisonSwitch(node)) {
                changed = true;
                break;
            }
        }
        if (changed) {
            continue;
        }

        /*
         * Try to reduce various kinds of regions.
         */
        foreach (Node *node, dfs.postordering()) {
            if (reduceCompoundCondition(node)) {
                changed = true;
                break;
            }
        }
        if (changed) {
            continue;
        }

        foreach (Node *node, dfs.postordering()) {
            if (reduceCyclic(node, dfs)) {
                changed = true;
                break;
            }
        }
        if (changed) {
            continue;
        }

        foreach (Node *node, dfs.postordering()) {
            if (reduceBlock(node)) {
                changed = true;
                break;
            }
        }
        if (changed) {
            continue;
        }

        foreach (Node *node, dfs.postordering()) {
            if (reduceConditional(node)) {
                changed = true;
                break;
            }
        }
        if (changed) {
            continue;
        }

        foreach (Node *node, dfs.postordering()) {
            if (reduceSwitch(node) || reduceHopelessConditional(node)) {
                changed = true;
                break;
            }
        }
        if (changed) {
            continue;
        }
    } while (changed);
}

bool StructureAnalyzer::reduceBlock(Node *entry) {
    Node *uniquePredecessor = entry->uniquePredecessor();

    /*
     * Blocks are only needed for reducing ifs.
     * If the unique predecessor cannot be an if condition, stop.
     */
    if (!uniquePredecessor || !uniquePredecessor->isFork() || !uniquePredecessor->isCondition()) {
        return false;
    }

    /* Discover all the nodes in the block. */
    std::vector<Node *> traverse;
    Node *node = entry;
    do {
        traverse.push_back(node);
        node = node->uniqueSuccessor();
    } while (node && node->uniquePredecessor());

    /* Finally, create the subregion. */
    if (traverse.size() > 1) {
        auto subregion = std::make_unique<Region>(Region::BLOCK);
        subregion->setEntry(entry);
        subregion->nodes() = std::move(traverse);
        return insertSubregion(entry->parent(), std::move(subregion));
    }

    return false;
}

bool StructureAnalyzer::reduceConditional(Node *entry) {
    if (!entry->isFork() || !entry->isCondition()) {
        return false;
    }

    Node *left = entry->outEdges()[0]->head();
    Node *right = entry->outEdges()[1]->head();

    /*
     * IF_THEN_ELSE
     */
    if (left->inEdges().size() == 1 && right->inEdges().size() == 1 &&
        left->outEdges().size() <= 1 && right->outEdges().size() <= 1 &&
        (left->outEdges().empty() || right->outEdges().empty() ||
         left->outEdges()[0]->head() == right->outEdges()[0]->head()))
    {
        auto subregion = std::make_unique<Region>(Region::IF_THEN_ELSE);
        subregion->setEntry(entry);
        subregion->nodes().push_back(entry);
        subregion->nodes().push_back(left);
        subregion->nodes().push_back(right);
        return insertSubregion(entry->parent(), std::move(subregion));
    }

    /*
     * IF_THEN
     */
#define REDUCE(left, right)                                                         \
    if (left->inEdges().size() == 1 &&                                              \
        (left->outEdges().empty() ||                                                \
         (left->outEdges().size() == 1 && left->outEdges()[0]->head() == right)))   \
    {                                                                               \
        auto subregion = std::make_unique<Region>(Region::IF_THEN);                 \
        subregion->setEntry(entry);                                                 \
        subregion->nodes().push_back(entry);                                        \
        subregion->nodes().push_back(left);                                         \
        subregion->setExitBasicBlock(right->getEntryBasicBlock());                  \
        return insertSubregion(entry->parent(), std::move(subregion));              \
    }
    REDUCE(left, right)
    REDUCE(right, left)
#undef REDUCE

    return false;
}

bool StructureAnalyzer::reduceHopelessConditional(Node *entry) {
    if (!entry->isFork() || !entry->isCondition()) {
        return false;
    }

    Node *left = entry->outEdges()[0]->head();
    Node *right = entry->outEdges()[1]->head();

    auto subregion = std::make_unique<Region>(Region::IF_THEN_ELSE);
    subregion->setEntry(entry);
    subregion->nodes().push_back(entry);
    subregion->nodes().push_back(left);
    subregion->nodes().push_back(right);
    return insertSubregion(entry->parent(), std::move(subregion));
}

bool StructureAnalyzer::reduceCompoundCondition(Node *entry) {
    if (!entry->isFork() || !entry->isCondition()) {
        return false;
    }

    Node *left = entry->outEdges()[0]->head();
    Node *right = entry->outEdges()[1]->head();

#define REDUCE(left, right)                                                                 \
    if (left->inEdges().size() == 1 && left->isFork() && left->isCondition() &&             \
        ((left->outEdges()[0]->head() == right && left->outEdges()[1]->head() != entry) ||  \
         (left->outEdges()[1]->head() == right && left->outEdges()[0]->head() != entry)))   \
    {                                                                                       \
        auto subregion = std::make_unique<Region>(Region::COMPOUND_CONDITION);              \
        subregion->setEntry(entry);                                                         \
        subregion->nodes().push_back(entry);                                                \
        subregion->nodes().push_back(left);                                                 \
        return insertSubregion(entry->parent(), std::move(subregion));                      \
    }
    REDUCE(left, right)
    REDUCE(right, left)
#undef REDUCE

    return false;
}

namespace {

struct LoopDescription {
    Region::RegionKind kind;
    Node *condition;
    Node *bodyEntry;
    Node *exitNode;

    LoopDescription(Region::RegionKind kind, Node *condition, Node *bodyEntry, Node *exitNode):
        kind(kind), condition(condition), bodyEntry(bodyEntry), exitNode(exitNode)
    {}
};

} // anonymous namespace

bool StructureAnalyzer::reduceCyclic(Node *entry, const Dfs &dfs) {
    /*
     * Try to find the nodes constituting the loop.
     */
    LoopExplorer explorer(entry, dfs);

    if (explorer.loopNodes().empty()) {
        return false;
    }

    /*
     * Create the region.
     */
    auto subregion = std::make_unique<Region>(Region::LOOP);
    subregion->setEntry(entry);
    subregion->nodes() = std::move(explorer.loopNodes());

    /*
     * Potential condition nodes, together with the respective loop
     * exit blocks. We need to compute it before doing the structural
     * analysis on the loop subregion, because we need the edges before
     * their redirection by insertSubregion().
     */
    std::vector<LoopDescription> loopDescriptions;

    auto detectLoop = [&](Region::RegionKind kind, Node *condition, Node *bodyEntry, Node *loopExit) {
        if (!nc::contains(subregion->nodes(), loopExit)) {
            assert(nc::contains(subregion->nodes(), bodyEntry));
            loopDescriptions.push_back(LoopDescription(kind, condition, bodyEntry, loopExit));
        }
    };

    /*
     * For a DO_WHILE loop.
     */
    foreach (Edge *edge, entry->inEdges()) {
        if (dfs.getEdgeType(edge) == Dfs::BACK) {
            Node *n = edge->tail();
            if (n->isFork() && n->isCondition()) {
                detectLoop(Region::DO_WHILE, n, n->outEdges()[0]->head(), n->outEdges()[1]->head());
                detectLoop(Region::DO_WHILE, n, n->outEdges()[1]->head(), n->outEdges()[0]->head());
            }
        }
    }

    /*
     * For a WHILE loop.
     */
    if (entry->isFork() && entry->isCondition()) {
        detectLoop(Region::WHILE, entry, entry->outEdges()[0]->head(), entry->outEdges()[1]->head());
        detectLoop(Region::WHILE, entry, entry->outEdges()[1]->head(), entry->outEdges()[0]->head());
    }

    /*
     * Insert the subregion, redirect edges.
     */
    Region *loop = insertSubregion(entry->parent(), std::move(subregion));
    if (!loop) {
        return false;
    }

    /*
     * Remove 'continue' edges. They only make the structural
     * analysis in the loop region harder.
     */
    std::vector<Edge *> continueEdges = entry->inEdges();
    foreach (Edge *edge, continueEdges) {
        edge->setTail(nullptr);
        edge->setHead(nullptr);
    }

    /*
     * Run structural analysis inside the loop region.
     */
    analyze(loop);

    /*
     * Try to find a condition node.
     */
    foreach (const auto &description, loopDescriptions) {
        if (description.condition->parent() == loop) {
            if (description.kind == Region::WHILE) {
                /*
                 * analyze() could put the body entry somewhere
                 * in the middle of some other region, in which
                 * case we will not be able to fall through into
                 * it from the while condition.
                 */
                auto uniqueSuccessor = description.condition->uniqueSuccessor();
                if (!uniqueSuccessor ||
                    description.bodyEntry->getEntryBasicBlock() != uniqueSuccessor->getEntryBasicBlock()) {
                    continue;
                }
            }

            loop->setRegionKind(description.kind);
            loop->setLoopCondition(description.condition);
            loop->setExitBasicBlock(description.exitNode->getEntryBasicBlock());
            break;
        }
    }

    return true;
}

namespace {

/** Normalized meaning of one conditional equality dispatch. */
struct EqualityDispatch {
    const Term *selector;
    ConstantValue value;
    bool equalityWhenTrue;

    EqualityDispatch():
        selector(nullptr), value(0), equalityWhenTrue(false)
    {}
};

bool isRegisterLocation(const MemoryLocation &location) {
    return location &&
        location.domain() >= MemoryDomain::FIRST_REGISTER &&
        location.domain() <= MemoryDomain::LAST_REGISTER;
}

bool isResolvedStackLocation(const MemoryLocation &location) {
    return location && location.domain() == MemoryDomain::STACK;
}

bool isAnalysisOnlyStatement(const Statement *statement) {
    return statement &&
        (statement->kind() == Statement::CALLBACK ||
         statement->kind() == Statement::REMEMBER_REACHING_DEFINITIONS);
}

/**
 * A switch evaluates its selector once, at the first dispatch.  Pure scalar
 * expressions are immediately suitable.  Additionally permit expressions
 * containing a resolved current-frame stack read: although a Dereference is
 * not generally speculative, this read was already unconditionally evaluated
 * by the first comparison and provenance proves its exact definition.
 */
bool isSafeSwitchSelector(const Term *term,
                          const dflow::Dataflow &dataflow) {
    if (!term || !term->isRead()) {
        return false;
    }
    if (effects::ExpressionEffects::analyze(
            term, dataflow).canEvaluateSpeculatively())
    {
        return true;
    }

    switch (term->kind()) {
        case Term::MEMORY_LOCATION_ACCESS:
            return isResolvedStackLocation(
                dataflow.getMemoryLocation(term));

        case Term::DEREFERENCE:
            /* Exact STACK resolution excludes globals and unresolved pointer
             * reads.  Keep the effective-address expression itself pure so
             * evaluating the source-level selector cannot introduce another
             * observable read. */
            return isResolvedStackLocation(
                       dataflow.getMemoryLocation(term)) &&
                effects::ExpressionEffects::analyze(
                    term->asDereference()->address(), dataflow)
                    .canEvaluateSpeculatively();

        case Term::UNARY_OPERATOR:
            return isSafeSwitchSelector(
                term->asUnaryOperator()->operand(), dataflow);

        case Term::BINARY_OPERATOR: {
            const BinaryOperator *binary = term->asBinaryOperator();
            switch (binary->operatorKind()) {
                case BinaryOperator::SIGNED_DIV:
                case BinaryOperator::SIGNED_REM:
                case BinaryOperator::UNSIGNED_DIV:
                case BinaryOperator::UNSIGNED_REM:
                    return false;
                default:
                    return isSafeSwitchSelector(binary->left(), dataflow) &&
                        isSafeSwitchSelector(binary->right(), dataflow);
            }
        }

        case Term::INT_CONST:
        case Term::INTRINSIC:
            return false;
    }
    return false;
}

/** True when an expression reads any part of a location. */
bool readsLocation(const Term *term, const MemoryLocation &location,
                   const dflow::Dataflow &dataflow) {
    if (!term || !location) {
        return false;
    }
    const MemoryLocation &termLocation =
        dataflow.getMemoryLocation(term);
    if (term->isRead() && termLocation &&
        termLocation.overlaps(location))
    {
        return true;
    }

    bool result = false;
    term->callOnChildren([&](const Term *child) {
        if (!result && readsLocation(child, location, dataflow)) {
            result = true;
        }
    });
    return result;
}

/**
 * Determines whether an expression may be moved past, or discarded after,
 * an already successful evaluation of the selector.  This accounts for x86
 * flag micro-assignments which repeat the same operand for several flags.
 * A trapping/observable read is accepted only when semantic identity proves
 * that it is the same resolved stack selector value.
 */
bool isHarmlessRepeatedComputation(
        const Term *term, const Term *selector,
        const dflow::Dataflow &dataflow,
        const dflow::ExpressionIdentity &identity,
        bool discarding) {
    if (!term) {
        return false;
    }

    const effects::ExpressionEffects termEffects =
        effects::ExpressionEffects::analyze(term, dataflow);
    if (discarding ? termEffects.canDiscard() :
                     termEffects.canEvaluateSpeculatively()) {
        return true;
    }
    if (isSafeSwitchSelector(term, dataflow) &&
        identity.areIdentical(term, selector))
    {
        return true;
    }

    switch (term->kind()) {
        case Term::UNARY_OPERATOR:
            return isHarmlessRepeatedComputation(
                term->asUnaryOperator()->operand(), selector, dataflow,
                identity, discarding);

        case Term::BINARY_OPERATOR: {
            const BinaryOperator *binary = term->asBinaryOperator();
            switch (binary->operatorKind()) {
                case BinaryOperator::SIGNED_DIV:
                case BinaryOperator::SIGNED_REM:
                case BinaryOperator::UNSIGNED_DIV:
                case BinaryOperator::UNSIGNED_REM:
                    return false;
                default:
                    return isHarmlessRepeatedComputation(
                               binary->left(), selector, dataflow,
                               identity, discarding) &&
                        isHarmlessRepeatedComputation(
                               binary->right(), selector, dataflow,
                               identity, discarding);
            }
        }

        case Term::INT_CONST:
        case Term::INTRINSIC:
        case Term::MEMORY_LOCATION_ACCESS:
        case Term::DEREFERENCE:
            return false;
    }
    return false;
}

/**
 * Code generation keeps statements preceding the first comparison but emits
 * the switch expression at the end of that block.  Prove that this small
 * delay crosses only effect-free register assignments and no write to any
 * location read by the selector.
 */
bool canDelayFirstSelector(
        const BasicNode *node, const Term *selector,
        const dflow::Dataflow &dataflow,
        const dflow::DefUseGraph &defUse,
        const dflow::ExpressionIdentity &identity) {
    if (!node || !selector || !selector->statement() ||
        selector->statement()->basicBlock() != node->basicBlock())
    {
        return false;
    }

    const BasicBlock *block = node->basicBlock();
    const Jump *jump = block->getJump();
    bool afterSelector = false;
    foreach (const Statement *statement, block->statements()) {
        if (statement == selector->statement()) {
            afterSelector = true;
            if (statement == jump) {
                return true;
            }
            continue;
        }
        if (!afterSelector) {
            continue;
        }
        if (statement == jump) {
            return true;
        }
        if (isAnalysisOnlyStatement(statement)) {
            continue;
        }

        const Assignment *assignment = statement->asAssignment();
        if (!assignment ||
            !assignment->left()->is<MemoryLocationAccess>() ||
            !isRegisterLocation(
                dataflow.getMemoryLocation(assignment->left())))
        {
            return false;
        }

        if (!isHarmlessRepeatedComputation(
                assignment->right(), selector, dataflow, identity, false))
        {
            /* A nonrepeatable value (for example an unknown machine flag)
             * may be dropped only when its definition is genuinely unused.
             * Otherwise moving the selector evaluation across it changes the
             * order of two dynamic observations. */
            if (!defUse.uses(assignment->left()).empty() ||
                !isHarmlessRepeatedComputation(
                    assignment->right(), selector, dataflow, identity, true))
            {
                return false;
            }
        }

        const MemoryLocation &written =
            dataflow.getMemoryLocation(assignment->left());
        if (readsLocation(selector, written, dataflow)) {
            return false;
        }
    }
    return false;
}

/**
 * Expands exactly one scalar register copy.  Unlike historical copy chasing,
 * this requires full bit coverage, one definition, dominance/order, and
 * complete provenance on every CFG path.
 */
const Term *expandExactCopy(
        const Term *term, const dflow::Dataflow &dataflow,
        const dflow::DefUseGraph &defUse,
        const dflow::ValueProvenance &provenance) {
    if (!term || !term->isRead() ||
        !term->is<MemoryLocationAccess>() ||
        !provenance.isPathComplete(term))
    {
        return term;
    }

    const MemoryLocation &location = dataflow.getMemoryLocation(term);
    const dflow::DefUseGraph::DefinitionSet &definitions =
        defUse.definitions(term);
    const Term *definition = definitions.uniqueDefinition();
    const Assignment *assignment = definition && definition->statement() ?
        definition->statement()->asAssignment() : nullptr;
    if (!isRegisterLocation(location) || !definitions.isComplete() ||
        definitions.location() != location || !definition ||
        dataflow.getMemoryLocation(definition) != location ||
        !assignment || assignment->left() != definition ||
        !assignment->right() ||
        assignment->right()->size() != term->size())
    {
        return term;
    }
    return assignment->right();
}

/** Resolves boolean copies and one-bit NOT operators around a condition. */
const Term *normalizeBooleanCondition(
        const Term *condition, bool &inverted,
        const dflow::Dataflow &dataflow,
        const dflow::DefUseGraph &defUse,
        const dflow::ValueProvenance &provenance) {
    inverted = false;
    const Term *term = condition;
    std::set<const Term *, std::less<const Term *>> visited;

    for (std::size_t depth = 0; term && depth < 32; ++depth) {
        if (!visited.insert(term).second) {
            return nullptr;
        }

        const Term *expanded =
            expandExactCopy(term, dataflow, defUse, provenance);
        if (expanded != term) {
            term = expanded;
            continue;
        }

        const UnaryOperator *unary = term->asUnaryOperator();
        if (unary && unary->operatorKind() == UnaryOperator::NOT &&
            unary->size() == 1 && unary->operand()->size() == 1)
        {
            inverted = !inverted;
            term = unary->operand();
            continue;
        }
        return term;
    }
    return nullptr;
}

/**
 * Recognizes a constant equality without consulting propagated concrete
 * values.  Besides a direct x == C, it accepts the width-preserving modular
 * identity emitted for machine CMP: (x - C) == 0 iff x == C.
 */
bool recognizeEqualityDispatch(
        const Jump *jump, EqualityDispatch &result,
        const dflow::Dataflow &dataflow,
        const dflow::DefUseGraph &defUse,
        const dflow::ValueProvenance &provenance) {
    if (!jump || !jump->isConditional() ||
        !jump->thenTarget().basicBlock() ||
        !jump->elseTarget().basicBlock())
    {
        return false;
    }

    bool inverted = false;
    const Term *condition = normalizeBooleanCondition(
        jump->condition(), inverted, dataflow, defUse, provenance);
    const BinaryOperator *equality = condition ?
        condition->asBinaryOperator() : nullptr;
    if (!equality || equality->operatorKind() != BinaryOperator::EQUAL ||
        equality->left()->size() != equality->right()->size())
    {
        return false;
    }

    const Term *left = equality->left();
    const Term *right = equality->right();
    const Constant *leftConstant = left->asConstant();
    const Constant *rightConstant = right->asConstant();

    const Term *selector = nullptr;
    const Constant *caseConstant = nullptr;

    /* CMP is lowered through a temporary subtraction and ZF. */
    const Constant *zero = leftConstant &&
            leftConstant->value().value() == 0 ? leftConstant :
        (rightConstant && rightConstant->value().value() == 0 ?
            rightConstant : nullptr);
    if (zero) {
        const Term *other = zero == leftConstant ? right : left;
        const Term *expanded =
            expandExactCopy(other, dataflow, defUse, provenance);
        const BinaryOperator *subtraction = expanded ?
            expanded->asBinaryOperator() : nullptr;
        if (subtraction &&
            subtraction->operatorKind() == BinaryOperator::SUB &&
            subtraction->size() == zero->size() &&
            subtraction->left()->size() == subtraction->right()->size())
        {
            const Constant *subLeft =
                subtraction->left()->asConstant();
            const Constant *subRight =
                subtraction->right()->asConstant();
            if (subLeft && !subRight) {
                selector = subtraction->right();
                caseConstant = subLeft;
            } else if (!subLeft && subRight) {
                selector = subtraction->left();
                caseConstant = subRight;
            }
        }
    }

    /* Direct equality is also a valid architecture-neutral form. */
    if (!selector) {
        if (leftConstant && !rightConstant) {
            selector = right;
            caseConstant = leftConstant;
        } else if (!leftConstant && rightConstant) {
            selector = left;
            caseConstant = rightConstant;
        }
    }

    if (!selector || !caseConstant ||
        selector->size() != caseConstant->size() ||
        !provenance.isPathComplete(selector) ||
        !isSafeSwitchSelector(selector, dataflow))
    {
        return false;
    }

    result.selector = selector;
    result.value = caseConstant->value().value();
    result.equalityWhenTrue = !inverted;
    return true;
}

BasicNode *findBasicNode(Region *region, const BasicBlock *basicBlock) {
    if (!region || !basicBlock) {
        return nullptr;
    }
    foreach (Node *node, region->nodes()) {
        BasicNode *basicNode = node->as<BasicNode>();
        if (basicNode && basicNode->basicBlock() == basicBlock) {
            return basicNode;
        }
    }
    return nullptr;
}

/**
 * Later comparisons disappear from generated code.  Accept their preludes
 * only when they are pure register computations whose definitions have no
 * users outside that same dispatch block.
 */
bool hasRemovablePrelude(
        const BasicNode *node, const dflow::Dataflow &dataflow,
        const dflow::DefUseGraph &defUse, const Term *selector,
        const dflow::ExpressionIdentity &identity) {
    if (!node || !node->basicBlock()->getJump()) {
        return false;
    }

    const BasicBlock *block = node->basicBlock();
    foreach (const Statement *statement, block->statements()) {
        if (statement == block->getJump()) {
            continue;
        }
        if (isAnalysisOnlyStatement(statement)) {
            continue;
        }

        const Assignment *assignment = statement->asAssignment();
        if (!assignment ||
            !assignment->left()->is<MemoryLocationAccess>() ||
            !isRegisterLocation(
                dataflow.getMemoryLocation(assignment->left())) ||
            !isHarmlessRepeatedComputation(
                assignment->right(), selector, dataflow, identity, true))
        {
            return false;
        }

        foreach (const dflow::DefUseGraph::Use &use,
                 defUse.uses(assignment->left())) {
            if (!use.term() || !use.term()->statement() ||
                use.term()->statement()->basicBlock() != block)
            {
                return false;
            }
        }
    }
    return true;
}

} // anonymous namespace

bool StructureAnalyzer::reduceComparisonSwitch(Node *entry) {
    BasicNode *first = entry ? entry->as<BasicNode>() : nullptr;
    Region *parent = entry ? entry->parent() : nullptr;
    if (!first || !parent || !dataflow_.converged()) {
        return false;
    }

    EqualityDispatch dispatch;
    if (!recognizeEqualityDispatch(
            first->basicBlock()->getJump(), dispatch, dataflow_, defUse_,
            provenance_))
    {
        return false;
    }

    const Term *selector = dispatch.selector;
    if (!canDelayFirstSelector(
            first, selector, dataflow_, defUse_, expressionIdentity_)) {
        return false;
    }
    std::vector<BasicNode *> dispatchNodes;
    std::vector<Switch::Case> cases;
    std::set<ConstantValue> values;
    std::set<Node *, std::less<Node *>> consumedDispatch;
    BasicNode *current = first;
    Node *defaultNode = nullptr;

    for (std::size_t count = 0;
         count < parent->nodes().size(); ++count) {
        if (!current || current->parent() != parent ||
            !consumedDispatch.insert(current).second ||
            (current != first &&
             !expressionIdentity_.areIdentical(
                 selector, dispatch.selector)) ||
            !values.insert(dispatch.value).second)
        {
            return false;
        }

        const Jump *jump = current->basicBlock()->getJump();
        const BasicBlock *caseBlock = dispatch.equalityWhenTrue ?
            jump->thenTarget().basicBlock() :
            jump->elseTarget().basicBlock();
        const BasicBlock *missBlock = dispatch.equalityWhenTrue ?
            jump->elseTarget().basicBlock() :
            jump->thenTarget().basicBlock();
        BasicNode *caseNode = findBasicNode(parent, caseBlock);
        BasicNode *missNode = findBasicNode(parent, missBlock);
        if (!caseNode || !missNode || caseNode == current ||
            missNode == current || !current->isFork() ||
            (current->outEdges()[0]->head() != caseNode &&
             current->outEdges()[1]->head() != caseNode) ||
            (current->outEdges()[0]->head() != missNode &&
             current->outEdges()[1]->head() != missNode))
        {
            return false;
        }

        dispatchNodes.push_back(current);
        cases.push_back(Switch::Case(dispatch.value, caseBlock));

        EqualityDispatch nextDispatch;
        const bool uniqueMissEntry =
            missNode->inEdges().size() == 1 &&
            missNode->inEdges().front()->tail() == current;
        if (uniqueMissEntry &&
            recognizeEqualityDispatch(
                missNode->basicBlock()->getJump(), nextDispatch,
                dataflow_, defUse_, provenance_) &&
            expressionIdentity_.areIdentical(
                selector, nextDispatch.selector))
        {
            if (values.find(nextDispatch.value) != values.end() ||
                !hasRemovablePrelude(
                    missNode, dataflow_, defUse_, nextDispatch.selector,
                    expressionIdentity_))
            {
                return false;
            }
            current = missNode;
            dispatch = nextDispatch;
            continue;
        }

        defaultNode = missNode;
        break;
    }

    /* A single comparison is clearer as an if and does not justify changing
     * the evaluation form. */
    if (dispatchNodes.size() < 2 || !defaultNode) {
        return false;
    }

    foreach (const Switch::Case &case_, cases) {
        BasicNode *caseNode = findBasicNode(parent, case_.basicBlock());
        if (!caseNode || consumedDispatch.find(caseNode) !=
                             consumedDispatch.end())
        {
            return false;
        }
    }
    if (consumedDispatch.find(defaultNode) != consumedDispatch.end()) {
        return false;
    }

    std::vector<const BasicBlock *> branchBlocks;
    foreach (const Switch::Case &case_, cases) {
        branchBlocks.push_back(case_.basicBlock());
    }
    branchBlocks.push_back(defaultNode->getEntryBasicBlock());
    const BasicBlock *mergeBlock =
        postdominators_.getNearestCommonPostDominator(branchBlocks);
    BasicNode *mergeNode = findBasicNode(parent, mergeBlock);
    if (!mergeBlock || !mergeNode ||
        consumedDispatch.find(mergeNode) != consumedDispatch.end())
    {
        return false;
    }
    foreach (const BasicBlock *branch, branchBlocks) {
        if (!postdominators_.isPostDominating(mergeBlock, branch)) {
            return false;
        }
    }

    std::set<Node *, std::less<Node *>> regionNodes = consumedDispatch;
    std::deque<Node *> worklist;
    foreach (const Switch::Case &case_, cases) {
        Node *caseNode = findBasicNode(parent, case_.basicBlock());
        if (caseNode != mergeNode) {
            worklist.push_back(caseNode);
        }
    }
    if (defaultNode != mergeNode) {
        worklist.push_back(defaultNode);
    }

    while (!worklist.empty()) {
        Node *node = worklist.front();
        worklist.pop_front();
        if (!node || node == mergeNode) {
            continue;
        }
        if (node->parent() != parent ||
            consumedDispatch.find(node) != consumedDispatch.end())
        {
            return false;
        }
        if (!regionNodes.insert(node).second) {
            continue;
        }
        foreach (Edge *edge, node->outEdges()) {
            if (edge->head() != mergeNode) {
                worklist.push_back(edge->head());
            }
        }
    }

    /* Prove one entry and one normal exit for the complete region.  Internal
     * edges between case bodies remain intact, so genuine fallthrough is
     * preserved rather than replaced with unconditional breaks. */
    foreach (Node *node, regionNodes) {
        foreach (Edge *edge, node->inEdges()) {
            const bool tailInside =
                regionNodes.find(edge->tail()) != regionNodes.end();
            if ((node == entry && tailInside) ||
                (node != entry && !tailInside))
            {
                return false;
            }
        }
        foreach (Edge *edge, node->outEdges()) {
            if (edge->head() != mergeNode &&
                regionNodes.find(edge->head()) == regionNodes.end())
            {
                return false;
            }
        }
    }

    auto subregion = std::make_unique<Switch>(
        selector, dispatchNodes, cases);
    subregion->setEntry(entry);
    subregion->setExitBasicBlock(mergeBlock);
    if (defaultNode != mergeNode) {
        subregion->setDefaultBasicBlock(
            defaultNode->getEntryBasicBlock());
    }
    foreach (Node *node, regionNodes) {
        subregion->nodes().push_back(node);
    }
    return insertSubregion(parent, std::move(subregion));
}

bool StructureAnalyzer::reduceSwitch(Node *entry) {
    if (!dataflow_.converged()) {
        /* Index tracing and bounds recognition consume propagated values.
         * Keep the explicit control flow when those facts did not reach a
         * fixpoint. */
        return false;
    }

    /*
     * Do not detect the same switch multiple times.
     */
    if (auto witch = entry->parent()->as<Switch>()) {
        if ((witch->isJumpTable() && witch->switchNode() == entry) ||
            (witch->isComparisonChain() &&
             nc::contains(witch->dispatchNodes(), entry)))
        {
            return false;
        }
    }

    /*
     * Entry must be a basic block node.
     */
    BasicNode *basicEntry = entry->as<BasicNode>();

    if (!basicEntry) {
        return false;
    }

    /*
     * Entry must end with an unconditional jump using a jump table,
     * and for which we can trace the jump index.
     */
    misc::ArrayAccess arrayAccess;
    std::size_t jumpTableSize;

    if (const Jump *jump = basicEntry->basicBlock()->getJump()) {
        if (jump->isUnconditional() && jump->thenTarget().table()) {
            arrayAccess = misc::recognizeArrayAccess(jump->thenTarget().address(), dataflow_);
            jumpTableSize = jump->thenTarget().table()->size();
        }
    }

    if (!arrayAccess) {
        return false;
    }

    /*
     * Typically, there is a bounds check before the switch:
     *
     * if (x < 10) {
     *     switch (x) {
     *       ...
     *     }
     * }
     */
    BasicNode *boundsCheckNode = nullptr;

    if (Node *node = entry->uniquePredecessor()) {
        if (BasicNode *basicBlockNode = node->as<BasicNode>()) {
            if (const Jump *jump = basicBlockNode->basicBlock()->getJump()) {
                if (auto boundsCheck = misc::recognizeBoundsCheck(jump, entry->getEntryBasicBlock(), dataflow_)) {
                    if (dflow::getFirstCopy(boundsCheck.index(), dataflow_) ==
                        dflow::getFirstCopy(arrayAccess.index(), dataflow_))
                    {
                        boundsCheckNode = basicBlockNode;
                        /* Convert the inclusive upper bound only after proving
                         * that it actually narrows the table.  Adding one in
                         * ConstantValue first would wrap UINT64_MAX to zero;
                         * converting first could truncate on a 32-bit host. */
                        if (boundsCheck.maxValue() <
                            static_cast<ConstantValue>(jumpTableSize))
                        {
                            jumpTableSize =
                                static_cast<std::size_t>(
                                    boundsCheck.maxValue()) + 1;
                        }
                    }
                }
            }
        }
    }

    /*
     * Node getting control if the bounds check fails is either an exit or a default.
     */
    Node *exitOrDefaultBranch = nullptr;

    if (boundsCheckNode) {
        exitOrDefaultBranch = boundsCheckNode->getOtherSuccessor(entry);
    }

    /*
     * Direct successors of entry node and exitOrDefaultBranch are branches of the switch.
     */
    std::vector<Node *> branches;

    foreach (Edge *edge, entry->outEdges()) {
        branches.push_back(edge->head());
    }

    if (exitOrDefaultBranch) {
        branches.push_back(exitOrDefaultBranch);
    }

    std::sort(branches.begin(), branches.end());
    branches.erase(std::unique(branches.begin(), branches.end()), branches.end());

    /*
     * Using BFS, for each branch, compute the nodes reachable solely from this branch.
     */
    boost::unordered_map<Node *, Node *> node2branch;
    std::queue<Node *> queue;

    foreach (Node *node, branches) {
        queue.push(node);
        node2branch[node] = node;
    }

    while (!queue.empty()) {
        foreach (Edge *outEdge, queue.front()->outEdges()) {
            if (!nc::find(node2branch, outEdge->head())) {
                Node *branch = nullptr;

                foreach (Edge *inEdge, outEdge->head()->inEdges()) {
                    if (Node *inBranch = nc::find(node2branch, inEdge->tail())) {
                        if (branch == nullptr) {
                            branch = inBranch;
                        } else if (branch != inBranch) {
                            branch = nullptr;
                            break;
                        }
                    } else {
                        branch = nullptr;
                        break;
                    }
                }

                if (branch != nullptr) {
                    node2branch[outEdge->head()] = branch;
                    queue.push(outEdge->head());
                }
            }
        }

        queue.pop();
    }

    /*
     * Returns how many branches actually join in the given node.
     */
    auto getJoinDegree = [&](const Node *node) -> std::size_t {
        std::vector<Node *> incomingBranches;

        foreach (const Edge *edge, node->inEdges()) {
            incomingBranches.push_back(find(node2branch, edge->tail()));
        }

        std::sort(incomingBranches.begin(), incomingBranches.end());
        incomingBranches.erase(std::unique(incomingBranches.begin(), incomingBranches.end()), incomingBranches.end());

        return incomingBranches.size();
    };

    /*
     * One of the branches can be actually an exit branch, i.e. go outside
     * the switch region.
     */
    Node *exitBranch = nullptr;

    /* More than so many other branches must join in the exit branch. */
    std::size_t exitBranchJoinDegree = 2;

    foreach (Node *branch, branches) {
        auto mergeDegree = getJoinDegree(branch);
        if (mergeDegree > exitBranchJoinDegree) {
            exitBranchJoinDegree = mergeDegree;
            exitBranch = branch;
        }
    }

    /* If bounds check does not lead to an exit, it leads to the default branch. */
    Node *defaultBranch = nullptr;

    if (exitBranch != exitOrDefaultBranch) {
        defaultBranch = exitOrDefaultBranch;
    }

    /*
     * Create the region.
     */
    auto subregion = std::make_unique<Switch>(basicEntry, arrayAccess.index(), jumpTableSize);

    subregion->nodes().push_back(entry);

    if (boundsCheckNode) {
        subregion->nodes().push_back(boundsCheckNode);
        subregion->setBoundsCheckNode(boundsCheckNode);
        subregion->setEntry(boundsCheckNode);
    } else {
        subregion->setEntry(entry);
    }

    if (exitBranch) {
        subregion->setExitBasicBlock(exitBranch->getEntryBasicBlock());
    }

    if (defaultBranch) {
        subregion->setDefaultBasicBlock(defaultBranch->getEntryBasicBlock());
    }

    foreach (const auto &pair, node2branch) {
        assert(pair.second != nullptr);

        if (pair.second != exitBranch) {
            subregion->nodes().push_back(pair.first);
        }
    }

    /*
     * Install this new region, redirect edges.
     */
    return insertSubregion(entry->parent(), std::move(subregion));
}

Region *StructureAnalyzer::insertSubregion(Region *region, std::unique_ptr<Region> subregion) {
    assert(region != nullptr);
    assert(subregion != nullptr);

    if (region->entry() == subregion->entry()) {
        region->setEntry(subregion.get());
    } else if (nc::contains(subregion->nodes(), region->entry())) {
        return nullptr;
    }

    foreach (auto node, subregion->nodes()) {
        node->setParent(subregion.get());
    }

    region->nodes().erase(
        std::remove_if(
            region->nodes().begin(),
            region->nodes().end(),
            [&](Node *n) { return n->parent() == subregion.get(); }),
        region->nodes().end());

    subregion->setParent(region);
    region->nodes().push_back(subregion.get());

    /*
     * Redirect edges properly.
     */

    std::vector<Edge *> edgesToSubregion;
    std::vector<Edge *> edgesFromSubregion;
    std::vector<Edge *> duplicateEdges;

    std::vector<Node *> tails;
    std::vector<Node *> heads;

    foreach (Node *node, subregion->nodes()) {
        foreach (Edge *edge, node->inEdges()) {
            assert(edge->tail()->parent() == region || edge->tail()->parent() == subregion.get());

            if (edge->tail()->parent() == region) {
                if (edge->head() == subregion->entry() && !nc::contains(tails, edge->tail())) {
                    edgesToSubregion.push_back(edge);
                    tails.push_back(edge->tail());
                } else {
                    duplicateEdges.push_back(edge);
                }
            }
        }
        foreach (Edge *edge, node->outEdges()) {
            assert(edge->head()->parent() == region || edge->head()->parent() == subregion.get());

            if (edge->head()->parent() == region) {
                if (!nc::contains(heads, edge->head())) {
                    edgesFromSubregion.push_back(edge);
                    heads.push_back(edge->head());
                } else {
                    duplicateEdges.push_back(edge);
                }
            }
        }
    }

    foreach (Edge *edge, edgesToSubregion) {
        edge->setHead(subregion.get());
    }
    foreach (Edge *edge, edgesFromSubregion) {
        edge->setTail(subregion.get());
    }
    foreach (Edge *edge, duplicateEdges) {
        edge->setTail(nullptr);
        edge->setHead(nullptr);
    }

    return graph_.addNode(std::move(subregion));
}

} // namespace cflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
