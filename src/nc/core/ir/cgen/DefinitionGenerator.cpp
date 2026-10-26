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

#include "DefinitionGenerator.h"

#include <functional>
#include <limits>

#include <nc/common/Foreach.h>
#include <nc/common/Range.h>
#include <nc/common/Unreachable.h>
#include <nc/common/make_unique.h>

#include <nc/core/arch/Architecture.h>
#include <nc/core/arch/Instruction.h>
#include <nc/core/image/Image.h>
#ifdef NC_PREFER_CSTRINGS_TO_CONSTANTS
#include <nc/core/image/Reader.h>
#include <nc/core/image/Section.h>
#endif
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallHook.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/EntryHook.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/calling/ReturnHook.h>
#include <nc/core/ir/cflow/BasicNode.h>
#include <nc/core/ir/cflow/Dfs.h>
#include <nc/core/ir/cflow/Graphs.h>
#include <nc/core/ir/cflow/Switch.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/dflow/Uses.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/liveness/Livenesses.h>
#include <nc/core/ir/types/Type.h>
#include <nc/core/ir/types/Types.h>
#include <nc/core/ir/vars/Variables.h>
#include <nc/core/likec/BinaryOperator.h>
#include <nc/core/likec/Block.h>
#include <nc/core/likec/Break.h>
#include <nc/core/likec/CallOperator.h>
#include <nc/core/likec/CaseLabel.h>
#include <nc/core/likec/Continue.h>
#include <nc/core/likec/DefaultLabel.h>
#include <nc/core/likec/DoWhile.h>
#include <nc/core/likec/ExpressionStatement.h>
#include <nc/core/likec/FunctionDefinition.h>
#include <nc/core/likec/FunctionIdentifier.h>
#include <nc/core/likec/Goto.h>
#include <nc/core/likec/If.h>
#include <nc/core/likec/InlineAssembly.h>
#include <nc/core/likec/IntegerConstant.h>
#include <nc/core/likec/LabelIdentifier.h>
#include <nc/core/likec/LabelStatement.h>
#include <nc/core/likec/Return.h>
#include <nc/core/likec/String.h>
#include <nc/core/likec/Switch.h>
#include <nc/core/likec/Tree.h>
#include <nc/core/likec/Typecast.h>
#include <nc/core/likec/Types.h>
#include <nc/core/likec/UnaryOperator.h>
#include <nc/core/likec/UndeclaredIdentifier.h>
#include <nc/core/likec/VariableIdentifier.h>
#include <nc/core/likec/While.h>

#include "SwitchContext.h"
#include "Utils.h"

namespace nc {
namespace core {
namespace ir {
namespace cgen {

DefinitionGenerator::DefinitionGenerator(CodeGenerator &parent, const Function *function, const CancellationToken &canceled):
    DeclarationGenerator(parent, calling::CalleeId(function), parent.signatures().getSignature(function).get()),
    function_(function),
    dataflow_(*parent.dataflows().at(function)),
    graph_(*parent.graphs().at(function)),
    liveness_(*parent.livenesses().at(function)),
    uses_(std::make_unique<dflow::Uses>(dataflow_)),
    cfg_(std::make_unique<CFG>(function->basicBlocks())),
    dominators_(std::make_unique<Dominators>(*cfg_, canceled)),
    hookStatements_(getHookStatements(function, dataflow_, parent.hooks())),
    definition_(nullptr),
    suppressStackBufferExpressions_(false)
{
    assert(function != nullptr);
}

DefinitionGenerator::~DefinitionGenerator() {}

void DefinitionGenerator::setDefinition(likec::FunctionDefinition *definition) {
    assert(!definition_);
    definition_ = definition;
    setDeclaration(definition);
}

std::unique_ptr<likec::FunctionDefinition> DefinitionGenerator::createDefinition() {
    auto nameAndComment = parent().nameGenerator().getFunctionName(function_);
    if (signature()->prototype() && !signature()->prototype()->preferredName().isEmpty()) {
        nameAndComment.name() = signature()->prototype()->preferredName();
    }

    auto functionDefinition = std::make_unique<likec::FunctionDefinition>(tree(),
        std::move(nameAndComment.name()), makeReturnType(), signature()->variadic());

    functionDefinition->setComment(std::move(nameAndComment.comment()));

    setDefinition(functionDefinition.get());

    if (auto entryHook = parent().hooks().getEntryHook(function_)) {
        foreach (const auto &argument, signature()->arguments()) {
            auto term = entryHook->getArgumentTerm(argument.get());
            assert(term != nullptr && "Entry hook must have clones of all arguments in the signature.");
            assert(dataflow_.getMemoryLocation(term) && "Argument must have a memory location.");

            auto variable = parent().variables().getVariable(term);
            assert(variable != nullptr && "Each term with a memory location must belong to a variable.");

            if (variable->memoryLocation() == dataflow_.getMemoryLocation(term)) {
                auto &variableDeclaration = variableDeclarations_[variable];
                assert(!variableDeclaration);
                variableDeclaration = makeArgumentDeclaration(term);
            } else {
                auto variableDeclaration = makeArgumentDeclaration(term);
                definition()->block()->addStatement(std::make_unique<likec::ExpressionStatement>(
                    std::make_unique<likec::BinaryOperator>(
                        likec::BinaryOperator::ASSIGN,
                        makeVariableAccess(term),
                        std::make_unique<likec::VariableIdentifier>(variableDeclaration))));
            }
        }
    }

    SwitchContext switchContext;
    makeStatements(graph_.root(), definition()->block().get(), nullptr, nullptr, nullptr, switchContext);

    return functionDefinition;
}

const calling::TypeDescription *DefinitionGenerator::getCallResultType(
        const vars::Variable *variable) const {
    assert(variable != nullptr);

    const calling::TypeDescription *result = nullptr;

    foreach (const auto basicBlock, function_->basicBlocks()) {
        foreach (const auto statement, basicBlock->statements()) {
            const auto call = statement->asCall();
            if (!call) {
                continue;
            }

            const auto callSignature = parent().signatures().getSignature(call);
            if (!callSignature || !callSignature->prototype() || !callSignature->returnValue() ||
                callSignature->prototype()->returnType().kind() == calling::TypeDescription::VOID)
            {
                continue;
            }

            const auto callHook = parent().hooks().getCallHook(call);
            if (!callHook) {
                continue;
            }

            const auto returnTerm = callHook->getReturnValueTerm(callSignature->returnValue().get());
            if (!returnTerm || parent().variables().getVariable(returnTerm) != variable) {
                continue;
            }

            const auto &candidate = callSignature->prototype()->returnType();
            if (result && *result != candidate) {
                return nullptr;
            }
            result = &candidate;
        }
    }

    return result;
}

likec::VariableDeclaration *DefinitionGenerator::makeLocalVariableDeclaration(const vars::Variable *variable) {
    assert(variable != nullptr);
    assert(variable->isLocal());

    likec::VariableDeclaration *&result = variableDeclarations_[variable];
    if (!result) {
        auto nameAndComment = parent().nameGenerator().getLocalVariableName(variable->memoryLocation(), variableDeclarations_.size());
        const likec::Type *type = parent().makeVariableType(variable);
        if (const auto presentationType = getCallResultType(variable)) {
            type = makePresentationType(*presentationType);
        }

        auto variableDeclaration = std::make_unique<likec::VariableDeclaration>(
            std::move(nameAndComment.name()), type);
        variableDeclaration->setComment(std::move(nameAndComment.comment()));

        result = variableDeclaration.get();
        definition()->block()->addDeclaration(std::move(variableDeclaration));
    }
    return result;
}

likec::VariableDeclaration *DefinitionGenerator::makeVariableDeclaration(const vars::Variable *variable) {
    assert(variable != nullptr);

    if (variable->isGlobal()) {
        return parent().makeGlobalVariableDeclaration(variable);
    } else {
        return makeLocalVariableDeclaration(variable);
    }
}

likec::LabelDeclaration *DefinitionGenerator::makeLabel(const BasicBlock *basicBlock) {
    likec::LabelDeclaration *&result = labels_[basicBlock];
    if (!result) {
        auto label = std::make_unique<likec::LabelDeclaration>(
            basicBlock->address() ?
                QString("addr_%1_%2").arg(basicBlock->address().get(), 0, 16).arg(labels_.size()) :
                QString("label_%1").arg(labels_.size())
            );
        result = label.get();
        definition()->addLabel(std::move(label));
    }
    return result;
}

void DefinitionGenerator::addLabels(const BasicBlock *basicBlock, likec::Block *block, SwitchContext &switchContext) {
    assert(basicBlock != nullptr);
    assert(block != nullptr);

    /* Add usual label. */
    block->addStatement(
        std::make_unique<likec::LabelStatement>(std::make_unique<likec::LabelIdentifier>(makeLabel(basicBlock))));

    /* Add case labels. */
    if (basicBlock->address()) {
        if (basicBlock == switchContext.defaultBasicBlock()) {
            block->addStatement(std::make_unique<likec::DefaultLabel>());
        } else {
            foreach (ConstantValue value, switchContext.getCaseValues(*basicBlock->address())) {
                block->addStatement(std::make_unique<likec::CaseLabel>(
                    std::make_unique<likec::IntegerConstant>(value, switchContext.valueType())));
            }
        }
        switchContext.eraseCaseValues(*basicBlock->address());
    }
}

void DefinitionGenerator::makeStatements(const cflow::Node *node, likec::Block *block, const BasicBlock *nextBB, const BasicBlock *breakBB, const BasicBlock *continueBB, SwitchContext &switchContext) {
    switch (node->nodeKind()) {
    case cflow::Node::BASIC: {
        auto basicNode = node->as<cflow::BasicNode>();

        addLabels(basicNode->basicBlock(), block, switchContext);

        foreach (const ir::Statement *statement, basicNode->basicBlock()->statements()) {
            if (auto likecStatement = makeStatement(statement, nextBB, breakBB, continueBB)) {
                block->addStatement(std::move(likecStatement));
            }
        }

        break;
    }
    case cflow::Node::REGION: {
        auto region = node->as<cflow::Region>();

        switch (region->regionKind()) {
        case cflow::Region::UNKNOWN: {
            assert(region->nodes().size() > 0);

            /*
             * We tend to process nodes in DFS order because it is likely
             * to minimize the number of generated gotos.
             */
            makeStatements(cflow::Dfs(region).preordering(), block, nextBB, breakBB, continueBB, switchContext);
            break;
        }
        case cflow::Region::BLOCK: {
            assert(region->nodes().size() > 0);

            makeStatements(region->nodes(), block, nextBB, breakBB, continueBB, switchContext);
            break;
        }
        case cflow::Region::COMPOUND_CONDITION: {
            assert(region->nodes().size() == 2);

            makeStatements(region->nodes(), block, nextBB, breakBB, continueBB, switchContext);
            break;
        }
        case cflow::Region::IF_THEN_ELSE: {
            assert(region->nodes().size() == 3);

            std::unique_ptr<likec::Expression> condition(makeExpression(region->nodes()[0], block,
                region->nodes()[1]->getEntryBasicBlock(), region->nodes()[2]->getEntryBasicBlock(), switchContext));

            auto thenBlock = std::make_unique<likec::Block>();
            makeStatements(region->nodes()[1], thenBlock.get(), nextBB, breakBB, continueBB, switchContext);

            auto elseBlock = std::make_unique<likec::Block>();
            makeStatements(region->nodes()[2], elseBlock.get(), nextBB, breakBB, continueBB, switchContext);

            block->addStatement(std::make_unique<likec::If>(std::move(condition), std::move(thenBlock), std::move(elseBlock)));

            break;
        }
        case cflow::Region::IF_THEN: {
            assert(region->nodes().size() == 2);
            assert(region->exitBasicBlock() != nullptr);

            std::unique_ptr<likec::Expression> condition(makeExpression(region->nodes()[0], block,
                region->nodes()[1]->getEntryBasicBlock(), region->exitBasicBlock(), switchContext));

            auto thenBlock = std::make_unique<likec::Block>();
            makeStatements(region->nodes()[1], thenBlock.get(), nextBB, breakBB, continueBB, switchContext);

            block->addStatement(std::make_unique<likec::If>(std::move(condition), std::move(thenBlock)));

            break;
        }
        case cflow::Region::LOOP: {
            assert(region->nodes().size() > 0);

            auto condition = std::make_unique<likec::IntegerConstant>(1, tree().makeIntegerType(tree().intSize(), false));

            cflow::Dfs dfs(region);

            auto body = std::make_unique<likec::Block>();
            const BasicBlock *entryBB = region->entry()->getEntryBasicBlock();

            makeStatements(dfs.preordering(), body.get(), entryBB, nextBB, entryBB, switchContext);

            block->addStatement(std::make_unique<likec::While>(std::move(condition), std::move(body)));

            break;
        }
        case cflow::Region::WHILE: {
            assert(region->nodes().size() > 0);
            assert(region->exitBasicBlock() != nullptr);

            addLabels(region->entry()->getEntryBasicBlock(), block, switchContext);

            if (auto statement = makeRepneScasLength(region)) {
                block->addStatement(std::move(statement));

                if (auto jump = makeJump(region->exitBasicBlock(), nextBB, breakBB, continueBB)) {
                    block->addStatement(std::move(jump));
                }
                break;
            }

            if (auto statement = makeRepStos(region)) {
                block->addStatement(std::move(statement));

                if (auto jump = makeJump(region->exitBasicBlock(), nextBB, breakBB, continueBB)) {
                    block->addStatement(std::move(jump));
                }
                break;
            }

            auto condition = makeExpression(region->entry(), nullptr,
                region->entry()->uniqueSuccessor()->getEntryBasicBlock(),
                region->exitBasicBlock(), switchContext);

            cflow::Dfs dfs(region);
            auto &nodes = dfs.preordering();

            assert(nodes.front() == region->entry());
            nodes.erase(nodes.begin());

            auto body = std::make_unique<likec::Block>();
            const BasicBlock *conditionBB = region->entry()->getEntryBasicBlock();

            makeStatements(nodes, body.get(), conditionBB, region->exitBasicBlock(), conditionBB, switchContext);

            block->addStatement(std::make_unique<likec::While>(std::move(condition), std::move(body)));

            if (auto jump = makeJump(region->exitBasicBlock(), nextBB, breakBB, continueBB)) {
                block->addStatement(std::move(jump));
            }

            break;
        }
        case cflow::Region::DO_WHILE: {
            assert(region->nodes().size() > 0);
            assert(region->exitBasicBlock() != nullptr);
            assert(region->loopCondition() != nullptr);

            /*
             * REPNE SCASB has both the count check at the head and the ZF
             * check on the back edge. Depending on region reduction order it
             * can therefore be represented as either WHILE or DO_WHILE.
             */
            if (auto statement = makeRepneScasLength(region)) {
                addLabels(region->entry()->getEntryBasicBlock(), block, switchContext);
                block->addStatement(std::move(statement));

                if (auto jump = makeJump(region->exitBasicBlock(), nextBB, breakBB, continueBB)) {
                    block->addStatement(std::move(jump));
                }
                break;
            }

            cflow::Dfs dfs(region);
            auto &nodes = dfs.preordering();

            assert(nc::contains(nodes, region->loopCondition()));
            nodes.erase(std::find(nodes.begin(), nodes.end(), region->loopCondition()));

            auto body = std::make_unique<likec::Block>();
            const BasicBlock *conditionBB = region->loopCondition()->getEntryBasicBlock();

            makeStatements(nodes, body.get(), conditionBB, nextBB, conditionBB, switchContext);

            auto condition = makeExpression(region->loopCondition(), body.get(),
                region->entry()->getEntryBasicBlock(),
                region->exitBasicBlock(),
                switchContext);

            block->addStatement(std::make_unique<likec::DoWhile>(std::move(body), std::move(condition)));

            if (auto jump = makeJump(region->exitBasicBlock(), nextBB, breakBB, continueBB)) {
                block->addStatement(std::move(jump));
            }

            break;
        }
        case cflow::Region::SWITCH: {
            auto witch = region->as<cflow::Switch>();

            /*
             * Generates code for the basic block, except the code for its terminator.
             */
            auto makeStatementsButLast = [&](const BasicBlock *basicBlock) {
                addLabels(basicBlock, block, switchContext);

                auto iend = --basicBlock->statements().end();
                for (auto i = basicBlock->statements().begin(); i != iend; ++i) {
                    /* We do not care about breakBB and others: we will not create gotos. */
                    if (auto likecStatement = makeStatement(*i, nullptr, nullptr, nullptr)) {
                        block->addStatement(std::move(likecStatement));
                    }
                }
            };

            /* Generate code for the basic block doing the bounds check. */
            if (witch->boundsCheckNode()) {
                makeStatementsButLast(witch->boundsCheckNode()->basicBlock());
            }

            /* Generate code for the basic block with the table-based jump. */
            makeStatementsButLast(witch->switchNode()->basicBlock());

            /* The jump via the jump table. */
            const Jump *jump = witch->switchNode()->basicBlock()->getJump();
            assert(jump != nullptr);
            assert(jump->isUnconditional());

            /* The jump table. */
            const JumpTable *jumpTable = jump->thenTarget().table();
            assert(jumpTable != nullptr);

            /*
             * Make a new switch context.
             */
            SwitchContext newSwitchContext;

            newSwitchContext.setValueType(tree().makeIntegerType(witch->switchTerm()->size(), true));

            for (std::size_t i = 0, size = witch->jumpTableSize(); i < size; ++i) {
                newSwitchContext.addCaseValue((*jumpTable)[i].address(), i);
            }

            if (witch->defaultBasicBlock()) {
                newSwitchContext.setDefaultBasicBlock(witch->defaultBasicBlock());
            }

            /* Exit basic block of the switch. */
            const BasicBlock *exitBB = witch->exitBasicBlock();
            if (!exitBB) {
                exitBB = nextBB;
            }

            /*
             * Generate the switch expression.
             */
            auto expression = std::make_unique<likec::Typecast>(
                likec::Typecast::C_STYLE_CAST,
                newSwitchContext.valueType(),
                makeExpression(witch->switchTerm()));

            /*
             * Generate the body of the switch.
             */
            cflow::Dfs dfs(region);
            auto &nodes = dfs.preordering();

            nodes.erase(
                std::remove_if(nodes.begin(), nodes.end(),
                    [witch](const cflow::Node *node){ return node == witch->boundsCheckNode() || node == witch->switchNode(); }),
                nodes.end());

            auto body = std::make_unique<likec::Block>();

            makeStatements(nodes, body.get(), exitBB, exitBB, continueBB, newSwitchContext);

            /*
             * Generate case labels that were not generated before.
             */
            foreach (const auto &pair, newSwitchContext.caseValuesMap()) {
                foreach (ConstantValue value, pair.second) {
                    body->addStatement(std::make_unique<likec::CaseLabel>(
                        std::make_unique<likec::IntegerConstant>(value, newSwitchContext.valueType())));
                }
                body->addStatement(std::make_unique<likec::Goto>(
                    std::make_unique<likec::IntegerConstant>(
                        pair.first,
                        tree().makeIntegerType(tree().pointerSize(), true))));
            }

            /* Generate the switch. */
            block->addStatement(std::make_unique<likec::Switch>(std::move(expression), std::move(body)));

            /* Generate a jump to the exit basic block, if it's not the nextBB. */
            if (auto jump = makeJump(exitBB, nextBB, breakBB, continueBB)) {
                block->addStatement(std::move(jump));
            }

            break;
        }
        default:
            unreachable();
        }
        break;
    }
    default:
        unreachable();
    }
}

void DefinitionGenerator::makeStatements(const std::vector<cflow::Node *> &nodes, likec::Block *block, const BasicBlock *nextBB, const BasicBlock *breakBB, const BasicBlock *continueBB, SwitchContext &switchContext) {
    if (nodes.empty()) {
        return;
    }
    for (std::size_t i = 0, last = nodes.size() - 1; i != last; ++i) {
        makeStatements(nodes[i], block, nodes[i + 1]->getEntryBasicBlock(), breakBB, continueBB, switchContext);
    }
    makeStatements(nodes.back(), block, nextBB, breakBB, continueBB, switchContext);
}

std::unique_ptr<likec::Expression> DefinitionGenerator::makeExpression(const cflow::Node *node, likec::Block *block, const BasicBlock *thenBB, const BasicBlock *elseBB, SwitchContext &switchContext) {
    assert(node != nullptr);
    assert(thenBB != nullptr);
    assert(elseBB != nullptr);
    assert(node->isCondition() && "Can only generate expressions from condition nodes.");

    std::unique_ptr<likec::Expression> result;

    if (const cflow::BasicNode *basicNode = node->as<cflow::BasicNode>()) {
        if (block) {
            addLabels(basicNode->basicBlock(), block, switchContext);
        }

        foreach (const ir::Statement *statement, basicNode->basicBlock()->statements()) {
            std::unique_ptr<likec::Expression> expression;

            if (const Jump *jump = statement->asJump()) {
                assert(jump == basicNode->basicBlock()->getJump());

                expression = makeExpression(jump->condition());

                assert((jump->thenTarget().basicBlock() == thenBB && jump->elseTarget().basicBlock() == elseBB) ||
                       (jump->thenTarget().basicBlock() == elseBB && jump->elseTarget().basicBlock() == thenBB));

                if (jump->thenTarget().basicBlock() != thenBB) {
                    expression = std::make_unique<likec::UnaryOperator>(likec::UnaryOperator::LOGICAL_NOT,
                                                                        std::move(expression));
                }
            } else if (auto stmt = makeStatement(statement, nullptr, nullptr, nullptr)) {
                if (block) {
                    block->addStatement(std::move(stmt));
                } else if (likec::ExpressionStatement *expressionStatement = stmt->as<likec::ExpressionStatement>()) {
                    expression = expressionStatement->releaseExpression();
                }
            }

            if (expression) {
                if (!result) {
                    result = std::move(expression);
                } else {
                    result = std::make_unique<likec::BinaryOperator>(likec::BinaryOperator::COMMA,
                        std::move(result), std::move(expression));
                }
            }
        }
    } else if (const cflow::Region *region = node->as<cflow::Region>()) {
        assert(region->regionKind() == cflow::Region::COMPOUND_CONDITION);
        assert(region->nodes().size() == 2);

        /*
         * Distinguishing AND from OR:
         *
         * if (a || b) { then } { else }
         *
         * a -> then || b
         * b -> then || else
         *
         * if (a && b) { then } { else }
         *
         * a -> b || else
         * b -> then || else
         */

        const cflow::Node *n = region->nodes()[0];
        while (const cflow::Region *r = n->as<cflow::Region>()) {
            assert(r->regionKind() == cflow::Region::COMPOUND_CONDITION);
            assert(r->nodes().size() == 2);
            n = r->nodes()[1];
        }

        const cflow::BasicNode *b = n->as<cflow::BasicNode>();
        assert(b != nullptr);

        const Jump *j = b->basicBlock()->getJump();
        assert(j != nullptr);

        if (j->thenTarget().basicBlock() == thenBB || j->elseTarget().basicBlock() == thenBB) {
            auto left  = makeExpression(region->nodes()[0], block, thenBB, region->nodes()[1]->getEntryBasicBlock(), switchContext);
            auto right = makeExpression(region->nodes()[1], nullptr, thenBB, elseBB, switchContext);

            result = std::make_unique<likec::BinaryOperator>(likec::BinaryOperator::LOGICAL_OR,
                std::move(left), std::move(right));
        } else if (j->thenTarget().basicBlock() == elseBB || j->elseTarget().basicBlock() == elseBB) {
            auto left  = makeExpression(region->nodes()[0], block, region->nodes()[1]->getEntryBasicBlock(), elseBB, switchContext);
            auto right = makeExpression(region->nodes()[1], nullptr, thenBB, elseBB, switchContext);

            result = std::make_unique<likec::BinaryOperator>(likec::BinaryOperator::LOGICAL_AND,
                std::move(left), std::move(right));
        } else {
            assert(!"First component of compound condition must contain a jump to thenBB or elseBB.");
        }
    } else {
        assert(!"Node must be a basic block node or a region.");
    }

    assert(result != nullptr && "Something is very wrong.");

    return result;
}

std::unique_ptr<likec::Statement> DefinitionGenerator::makeStatement(const Statement *statement, const BasicBlock *nextBB, const BasicBlock *breakBB, const BasicBlock *continueBB) {
    assert(statement);

    if (nc::contains(hookStatements_, statement)) {
        return nullptr;
    }

    auto result = doMakeStatement(statement, nextBB, breakBB, continueBB);

    if (result != nullptr) {
        class StatementSetter {
            const ir::Statement *statement_;

        public:
            StatementSetter(const ir::Statement *statement): statement_(statement) {
                assert(statement != nullptr);
            }

            void operator()(likec::TreeNode *node) {
                if (auto stmt = node->as<likec::Statement>()) {
                    if (stmt->statement() == nullptr) {
                        stmt->setStatement(statement_);
                        stmt->callOnChildren(*this);
                    }
                }
            }
        };

        StatementSetter setter(statement);
        setter(result.get());
    }

    return result;
}

std::unique_ptr<likec::Statement> DefinitionGenerator::doMakeStatement(const Statement *statement, const BasicBlock *nextBB, const BasicBlock *breakBB, const BasicBlock *continueBB) {
    switch (statement->kind()) {
        case Statement::INLINE_ASSEMBLY: {
            return std::make_unique<likec::InlineAssembly>(
                statement->instruction() ? statement->instruction()->toString() : QString());
        }
        case Statement::ASSIGNMENT: {
            const Assignment *assignment = statement->asAssignment();

            if (!liveness_.isLive(assignment->left())) {
                return nullptr;
            }

            if (isSubstituted(assignment->left())) {
                return nullptr;
            }

            std::unique_ptr<likec::Expression> left(makeExpression(assignment->left()));
            std::unique_ptr<likec::Expression> right(makeExpression(assignment->right()));

            return std::make_unique<likec::ExpressionStatement>(
                std::make_unique<likec::BinaryOperator>(likec::BinaryOperator::ASSIGN,
                    std::move(left),
                    std::make_unique<likec::Typecast>(
                        likec::Typecast::C_STYLE_CAST,
                        parent().makeType(parent().types().getType(assignment->left())),
                        std::move(right))));
        }
        case Statement::JUMP: {
            const Jump *jump = statement->asJump();

            if (jump->isConditional()) {
                auto thenJump = makeJump(jump, jump->thenTarget(), nextBB, breakBB, continueBB);
                auto elseJump = makeJump(jump, jump->elseTarget(), nextBB, breakBB, continueBB);
                auto condition = makeExpression(jump->condition());

                if (thenJump == nullptr) {
                    if (elseJump == nullptr) {
                        return nullptr;
                    } else {
                        std::swap(thenJump, elseJump);
                        condition = std::make_unique<likec::UnaryOperator>(likec::UnaryOperator::LOGICAL_NOT, std::move(condition));
                    }
                }
                return std::make_unique<likec::If>(std::move(condition), std::move(thenJump), std::move(elseJump));
            } else {
                return makeJump(jump, jump->thenTarget(), nextBB, breakBB, continueBB);
            }
        }
        case Statement::CALL: {
            const Call *call = statement->asCall();

            std::unique_ptr<likec::Expression> target;

            auto targetValue = dataflow_.getValue(call->target());
            if (targetValue->abstractValue().isConcrete()) {
                if (auto functionDeclaration = parent().makeFunctionDeclaration(targetValue->abstractValue().asConcrete().value())) {
                    target = std::make_unique<likec::FunctionIdentifier>(functionDeclaration);
                    target->setTerm(call->target());
                }
            }

            if (!target) {
                target = makeExpression(call->target());
            }

            auto callOperator = std::make_unique<likec::CallOperator>(std::move(target));

            if (auto callSignature = parent().signatures().getSignature(call)) {
                if (auto callHook = parent().hooks().getCallHook(call)) {
                    foreach (const auto &argument, callSignature->arguments()) {
                        callOperator->addArgument(makeExpression(callHook->getArgumentTerm(argument.get())));
                    }

                    if (callSignature->returnValue()) {
                        const Term *returnValueTerm = callHook->getReturnValueTerm(callSignature->returnValue().get());

                        if (liveness_.isLive(returnValueTerm)) {
                            const likec::Type *returnType =
                                parent().makeType(parent().types().getType(returnValueTerm));
                            if (callSignature->prototype() &&
                                callSignature->prototype()->returnType().kind() != calling::TypeDescription::VOID)
                            {
                                returnType = makePresentationType(callSignature->prototype()->returnType());
                            }
                            return std::make_unique<likec::ExpressionStatement>(
                                std::make_unique<likec::BinaryOperator>(
                                    likec::BinaryOperator::ASSIGN,
                                    makeExpression(returnValueTerm),
                                    std::make_unique<likec::Typecast>(
                                        likec::Typecast::C_STYLE_CAST,
                                        returnType,
                                        std::move(callOperator))));
                        }
                    }
                }
            }

            return std::make_unique<likec::ExpressionStatement>(std::move(callOperator));
        }
        case Statement::HALT: {
            return nullptr;
        }
        case Statement::TOUCH: {
            return nullptr;
        }
        case Statement::CALLBACK: {
            return nullptr;
        }
        case Statement::REMEMBER_REACHING_DEFINITIONS: {
            return nullptr;
        }
        case Statement::STACK_MEMORY_INVALIDATION: {
            return nullptr;
        }
    }

    unreachable();
    return nullptr;
}

std::unique_ptr<likec::Statement> DefinitionGenerator::makeRepStos(const cflow::Region *region) {
    assert(region != nullptr);

    /*
     * A REP STOS instruction is expanded by the x86 front end into a small
     * synthetic CFG. Keep this recognition here, where the complete loop and
     * its dataflow are available, rather than guessing from an arbitrary
     * decrementing loop in the source-like tree.
     */
    std::vector<const Statement *> statements;
    std::function<void(const cflow::Node *)> collectStatements =
        [&](const cflow::Node *node) {
            if (auto basicNode = node->as<cflow::BasicNode>()) {
                foreach (const Statement *statement, basicNode->basicBlock()->statements()) {
                    statements.push_back(statement);
                }
            } else if (auto nestedRegion = node->as<cflow::Region>()) {
                foreach (const cflow::Node *nestedNode, nestedRegion->nodes()) {
                    collectStatements(nestedNode);
                }
            }
        };
    collectStatements(region);

    const arch::Instruction *instruction = nullptr;
    foreach (const Statement *statement, statements) {
        if (!statement->instruction()) {
            /* Replacing the region must not silently discard hook semantics. */
            return nullptr;
        }
        if (!instruction) {
            instruction = statement->instruction();
        } else if (statement->instruction() != instruction) {
            return nullptr;
        }
        if (!statement->asAssignment() && !statement->asJump()) {
            return nullptr;
        }
    }
    if (!instruction) {
        return nullptr;
    }

    const QString instructionText = instruction->toString().trimmed().toLower();
    if (!(instructionText.startsWith(QLatin1String("rep ")) ||
          instructionText.startsWith(QLatin1String("repz "))) ||
        !instructionText.contains(QLatin1String("stos")))
    {
        return nullptr;
    }

    const Assignment *memoryWrite = nullptr;
    const Assignment *countUpdate = nullptr;
    const Assignment *destinationUpdate = nullptr;
    const Term *countRead = nullptr;
    const Term *destinationRead = nullptr;
    std::vector<const Assignment *> auxiliaryAssignments;

    auto sameLocation = [&](const Term *left, const Term *right) {
        const MemoryLocation &leftLocation = dataflow_.getMemoryLocation(left);
        return leftLocation && leftLocation == dataflow_.getMemoryLocation(right);
    };
    auto concreteValue = [&](const Term *term, ConstantValue &result) {
        const dflow::Value *value = dataflow_.getValue(term);
        if (!value || !value->abstractValue().isConcrete()) {
            return false;
        }
        result = value->abstractValue().asConcrete().value();
        return true;
    };

    foreach (const Statement *statement, statements) {
        if (statement->instruction() != instruction) {
            continue;
        }

        const Assignment *assignment = statement->asAssignment();
        if (!assignment) {
            continue;
        }

        if (assignment->left()->is<Dereference>()) {
            if (memoryWrite) {
                return nullptr;
            }
            memoryWrite = assignment;
            continue;
        }

        const BinaryOperator *binary = assignment->right()->asBinaryOperator();
        if (!binary || !sameLocation(assignment->left(), binary->left())) {
            /*
             * The x86 front end also emits an instruction-local temporary
             * which computes the DF-dependent pointer increment.  It is not
             * architectural state and is expected to appear in this region.
             */
            auxiliaryAssignments.push_back(assignment);
            continue;
        }

        ConstantValue delta;
        if (!concreteValue(binary->right(), delta)) {
            auxiliaryAssignments.push_back(assignment);
            continue;
        }

        if (binary->operatorKind() == BinaryOperator::SUB && delta == 1) {
            if (countUpdate) {
                return nullptr;
            }
            countUpdate = assignment;
            countRead = binary->left();
        } else if (binary->operatorKind() == BinaryOperator::ADD) {
            if (destinationUpdate) {
                return nullptr;
            }
            destinationUpdate = assignment;
            destinationRead = binary->left();
        } else {
            auxiliaryAssignments.push_back(assignment);
        }
    }

    if (!memoryWrite || !countUpdate || !destinationUpdate || !countRead || !destinationRead) {
        return nullptr;
    }

    const Dereference *destinationDereference = memoryWrite->left()->asDereference();
    if (!destinationDereference || destinationDereference->domain() != MemoryDomain::MEMORY ||
        destinationDereference->size() % CHAR_BIT != 0)
    {
        return nullptr;
    }
    const ConstantValue elementBytes = destinationDereference->size() / CHAR_BIT;
    if (elementBytes == 0 ||
        !sameLocation(destinationDereference->address(), destinationRead)) {
        return nullptr;
    }

    /* A forward increment proves that DF was clear at this instruction. */
    const BinaryOperator *destinationExpression = destinationUpdate->right()->asBinaryOperator();
    ConstantValue destinationDelta;
    if (!destinationExpression ||
        !concreteValue(destinationExpression->right(), destinationDelta) ||
        destinationDelta != elementBytes)
    {
        return nullptr;
    }

    /*
     * Obtain the definition entering the synthetic loop, excluding its
     * loop-carried update. There must be one unambiguous external source.
     */
    auto initialSource = [&](const Term *read) -> const Term * {
        if (!read || !read->isRead()) {
            return nullptr;
        }

        const Term *result = nullptr;
        const dflow::ReachingDefinitions &definitions = dataflow_.getDefinitions(read);
        const MemoryLocation &readLocation = dataflow_.getMemoryLocation(read);
        if (!readLocation || definitions.chunks().empty()) {
            return nullptr;
        }

        BitAddr nextAddress = readLocation.addr();
        foreach (const dflow::ReachingDefinitions::Chunk &chunk, definitions.chunks()) {
            if (chunk.location().domain() != readLocation.domain() ||
                chunk.location().addr() != nextAddress ||
                chunk.hasUnknownDefinition())
            {
                return nullptr;
            }
            nextAddress = chunk.location().endAddr();
            foreach (const Term *definition, chunk.definitions()) {
                const Statement *sourceStatement = definition->statement();
                if (sourceStatement && sourceStatement->instruction() == instruction) {
                    continue;
                }
                if (!definition->source() || (result && result != definition->source())) {
                    return nullptr;
                }
                result = definition->source();
            }
        }
        if (nextAddress != readLocation.endAddr()) {
            return nullptr;
        }
        return result;
    };

    const Term *initialCount = initialSource(countRead);
    const Term *initialDestination = initialSource(destinationRead);
    if (!initialCount || !initialDestination) {
        return nullptr;
    }

    ConstantValue count;
    ConstantValue fillPattern;
    if (!concreteValue(initialCount, count) || !concreteValue(memoryWrite->right(), fillPattern)) {
        return nullptr;
    }

    /* memset is equivalent to STOS only for values made of one repeated byte. */
    const ConstantValue fillByte = fillPattern & 0xff;
    for (SmallBitSize shift = CHAR_BIT;
         shift < destinationDereference->size(); shift += CHAR_BIT) {
        if (((fillPattern >> shift) & 0xff) != fillByte) {
            return nullptr;
        }
    }
    if (count == 0 ||
        count > (std::numeric_limits<ConstantValue>::max)() / elementBytes) {
        return nullptr;
    }
    ConstantValue byteCount = count * elementBytes;
    if (bitTruncate(byteCount, tree().pointerSize()) != byteCount) {
        return nullptr;
    }
    const ConstantValue repByteCount = byteCount;

    /*
     * REP also leaves CX at zero and advances DI. Only hide the loop when
     * neither resulting architectural value is consumed afterwards.
     */
    auto hasExternalUse = [&](const Term *write) {
        foreach (const dflow::Uses::Use &use, uses_->getUses(write)) {
            if (!liveness_.isLive(use.term())) {
                continue;
            }
            const Statement *useStatement = use.term()->statement();
            if (!useStatement || useStatement->instruction() != instruction) {
                return true;
            }
        }
        return false;
    };
    if (hasExternalUse(countUpdate->left()) || hasExternalUse(destinationUpdate->left())) {
        return nullptr;
    }
    foreach (const Assignment *assignment, auxiliaryAssignments) {
        if (hasExternalUse(assignment->left())) {
            return nullptr;
        }
    }

    const Term *memsetDestination = initialDestination;

    /*
     * MSVC commonly clears an odd-sized local array with one fixed store
     * followed by REP STOS, for example 4 + 96 or 1 + 196 bytes.  Extend the
     * memset only when the immediately preceding memory range is written by
     * one dominating store of the same repeated byte and every path from that
     * store to the REP is free of other runtime memory accesses.  The latter
     * condition makes moving the prefix write to the REP point unobservable.
     */
    const auto repOffset = getProvenStackOffset(initialDestination);
    const BasicBlock *entryBlock = region->entry()->getEntryBasicBlock();
    const Statement *entryStatement =
        entryBlock && !entryBlock->statements().empty() ?
            entryBlock->statements().front() : nullptr;
    const Assignment *prefixStore = nullptr;
    const Term *prefixAddress = nullptr;
    ConstantValue prefixByteCount = 0;
    bool prefixStoreIsAmbiguous = false;

    std::function<bool(const Term *)> containsRuntimeMemoryAccess =
        [&](const Term *term) -> bool {
            if (!term) {
                return false;
            }
            if (term->is<Dereference>()) {
                return true;
            }
            if (const MemoryLocationAccess *access =
                    term->asMemoryLocationAccess())
            {
                if (access->memoryLocation().domain() == MemoryDomain::STACK ||
                    access->memoryLocation().domain() == MemoryDomain::MEMORY)
                {
                    return true;
                }
            }

            bool result = false;
            term->callOnChildren([&](const Term *child) {
                if (!result && containsRuntimeMemoryAccess(child)) {
                    result = true;
                }
            });
            return result;
        };

    auto isMemoryFreeStatement =
        [&](const Statement *statement) -> bool {
            if (const Assignment *assignment = statement->asAssignment()) {
                return !containsRuntimeMemoryAccess(assignment->left()) &&
                       !containsRuntimeMemoryAccess(assignment->right());
            }
            if (const Jump *jump = statement->asJump()) {
                return !containsRuntimeMemoryAccess(jump->condition()) &&
                       !containsRuntimeMemoryAccess(jump->thenTarget().address()) &&
                       !containsRuntimeMemoryAccess(jump->elseTarget().address());
            }
            return statement->kind() == Statement::CALLBACK ||
                   statement->kind() == Statement::REMEMBER_REACHING_DEFINITIONS;
        };

    auto isOnControlFlowCycle = [&](const BasicBlock *start) -> bool {
        boost::unordered_set<const BasicBlock *> visited;
        std::vector<const BasicBlock *> pending(
            cfg_->getSuccessors(start).begin(), cfg_->getSuccessors(start).end());
        while (!pending.empty()) {
            const BasicBlock *basicBlock = pending.back();
            pending.pop_back();
            if (basicBlock == start) {
                return true;
            }
            if (!visited.insert(basicBlock).second) {
                continue;
            }
            const auto &successors = cfg_->getSuccessors(basicBlock);
            pending.insert(pending.end(), successors.begin(), successors.end());
        }
        return false;
    };

    if (repOffset && entryStatement) {
        foreach (const BasicBlock *basicBlock, function_->basicBlocks()) {
            foreach (const Statement *statement, basicBlock->statements()) {
                const Assignment *candidate = statement->asAssignment();
                if (!candidate || !candidate->instruction() ||
                    candidate->instruction() == instruction ||
                    candidate->instruction()->addr() >= instruction->addr())
                {
                    continue;
                }

                const Dereference *prefixDereference =
                    candidate->left()->asDereference();
                if (!prefixDereference ||
                    prefixDereference->domain() != MemoryDomain::MEMORY ||
                    containsRuntimeMemoryAccess(candidate->right()) ||
                    prefixDereference->size() <= 0 ||
                    prefixDereference->size() % CHAR_BIT != 0 ||
                    prefixDereference->size() >
                        std::numeric_limits<ConstantValue>::digits)
                {
                    continue;
                }

                const auto candidateOffset =
                    getProvenStackOffset(prefixDereference->address());
                const SignedConstantValue candidateBytes =
                    prefixDereference->size() / CHAR_BIT;
                if (!candidateOffset ||
                    *repOffset <
                        (std::numeric_limits<SignedConstantValue>::min)() +
                            candidateBytes ||
                    *candidateOffset != *repOffset - candidateBytes)
                {
                    continue;
                }

                const MemoryLocation &candidateLocation =
                    dataflow_.getMemoryLocation(candidate->left());
                if (!candidateLocation ||
                    candidateLocation.domain() != MemoryDomain::STACK ||
                    candidateLocation.size() != prefixDereference->size() ||
                    candidateLocation.addr() % CHAR_BIT != 0 ||
                    candidateLocation.addr() / CHAR_BIT != *candidateOffset)
                {
                    continue;
                }

                ConstantValue candidatePattern;
                if (!concreteValue(candidate->right(), candidatePattern)) {
                    continue;
                }
                bool sameFill = true;
                for (SmallBitSize shift = 0;
                     shift < prefixDereference->size(); shift += CHAR_BIT) {
                    if (((candidatePattern >> shift) & 0xff) != fillByte) {
                        sameFill = false;
                        break;
                    }
                }
                if (!sameFill ||
                    !isDominating(candidate, entryStatement, *dominators_) ||
                    isOnControlFlowCycle(candidate->basicBlock()))
                {
                    continue;
                }

                /* Removing the original store is safe only on a linear path. */
                bool linearPath = true;
                boost::unordered_set<const BasicBlock *> visitedBlocks;
                const BasicBlock *pathBlock = candidate->basicBlock();
                while (pathBlock != entryBlock) {
                    if (!visitedBlocks.insert(pathBlock).second) {
                        linearPath = false;
                        break;
                    }
                    const auto &successors = cfg_->getSuccessors(pathBlock);
                    if (successors.size() != 1) {
                        linearPath = false;
                        break;
                    }
                    pathBlock = successors.front();
                }
                if (!linearPath) {
                    continue;
                }

                const auto memoryFreePath = allOfStatementsBetween(
                    candidate, entryStatement, *cfg_,
                    [&](const Statement *between) -> bool {
                        if (between == candidate) {
                            return true;
                        }
                        return isMemoryFreeStatement(between);
                    });
                if (memoryFreePath != true) {
                    continue;
                }

                /* More than one qualifying store means the proof is ambiguous. */
                if (prefixStore) {
                    prefixStore = nullptr;
                    prefixAddress = nullptr;
                    prefixByteCount = 0;
                    prefixStoreIsAmbiguous = true;
                    break;
                }
                prefixStore = candidate;
                prefixAddress = prefixDereference->address();
                prefixByteCount = static_cast<ConstantValue>(candidateBytes);
            }
            if (prefixStoreIsAmbiguous) {
                break;
            }
        }
    }

    auto eraseGeneratedStatement = [&](const Statement *source) -> bool {
        std::function<bool(likec::TreeNode *)> eraseFromNode;
        std::function<bool(likec::Block *)> eraseFromBlock;
        eraseFromNode = [&](likec::TreeNode *node) -> bool {
            if (likec::Statement *statement = node->as<likec::Statement>()) {
                if (likec::Block *nestedBlock = statement->as<likec::Block>()) {
                    return eraseFromBlock(nestedBlock);
                }
            }
            bool erased = false;
            node->callOnChildren([&](likec::TreeNode *child) {
                if (!erased) {
                    erased = eraseFromNode(child);
                }
            });
            return erased;
        };
        eraseFromBlock = [&](likec::Block *sourceBlock) -> bool {
            auto &generatedStatements = sourceBlock->statements();
            for (auto i = generatedStatements.begin();
                 i != generatedStatements.end(); ++i)
            {
                if ((*i)->statement() == source) {
                    generatedStatements.erase(i);
                    return true;
                }
                if (eraseFromNode(i->get())) {
                    return true;
                }
            }
            return false;
        };
        return eraseFromBlock(definition()->block().get());
    };

    if (!prefixStoreIsAmbiguous && prefixStore &&
        prefixByteCount <= (std::numeric_limits<ConstantValue>::max)() - byteCount)
    {
        const ConstantValue extendedByteCount = byteCount + prefixByteCount;
        const auto extendedOffset = getProvenStackOffset(prefixAddress);
        const bool localRangeIsValid =
            extendedOffset && *extendedOffset < 0 &&
            extendedByteCount <=
                static_cast<ConstantValue>(-(*extendedOffset + 1)) + 1;
        if (localRangeIsValid &&
            bitTruncate(extendedByteCount, tree().pointerSize()) ==
                extendedByteCount)
        {
            /*
             * The prefix node may already have been emitted because source
             * generation reaches it before this REP region. Remove precisely
             * that one generated statement. If it was substituted or dead,
             * there is no standalone AST node to remove.
             */
            const bool erasedPrefix = eraseGeneratedStatement(prefixStore);
            const bool prefixHasNoStandaloneStatement =
                !liveness_.isLive(prefixStore->left()) ||
                isSubstituted(prefixStore->left());
            if (erasedPrefix || prefixHasNoStandaloneStatement) {
                memsetDestination = prefixAddress;
                byteCount = extendedByteCount;
            }
        }
    }

    /*
     * The remainder can instead be emitted after REP STOS (typically a
     * trailing STOSB). Fold that store only when REP's exit reaches it through
     * a single, memory-free path and its stack range begins exactly where the
     * repeated range ends.
     */
    const Assignment *suffixStore = nullptr;
    ConstantValue suffixByteCount = 0;
    bool suffixStoreIsAmbiguous = false;
    const BasicBlock *exitBlock = region->exitBasicBlock();

    SignedConstantValue repEndOffset = 0;
    const bool haveRepEndOffset =
        repOffset &&
        repByteCount <= static_cast<ConstantValue>(
            (std::numeric_limits<SignedConstantValue>::max)()) &&
        *repOffset <= (std::numeric_limits<SignedConstantValue>::max)() -
            static_cast<SignedConstantValue>(repByteCount);
    if (haveRepEndOffset) {
        repEndOffset = *repOffset + static_cast<SignedConstantValue>(repByteCount);
    }

    auto hasLinearMemoryFreePathFromExit =
        [&](const Assignment *candidate) -> bool {
            if (!exitBlock || !candidate || !candidate->basicBlock()) {
                return false;
            }

            boost::unordered_set<const BasicBlock *> visitedBlocks;
            const BasicBlock *pathBlock = exitBlock;
            while (true) {
                if (!visitedBlocks.insert(pathBlock).second) {
                    return false;
                }

                bool foundCandidate = false;
                foreach (const Statement *statement, pathBlock->statements()) {
                    if (statement == candidate) {
                        foundCandidate = true;
                        break;
                    }
                    if (!isMemoryFreeStatement(statement)) {
                        return false;
                    }
                }
                if (pathBlock == candidate->basicBlock()) {
                    return foundCandidate;
                }

                const auto &successors = cfg_->getSuccessors(pathBlock);
                if (successors.size() != 1) {
                    return false;
                }
                pathBlock = successors.front();
            }
        };

    if (haveRepEndOffset && entryStatement) {
        foreach (const BasicBlock *basicBlock, function_->basicBlocks()) {
            foreach (const Statement *statement, basicBlock->statements()) {
                const Assignment *candidate = statement->asAssignment();
                if (!candidate || !candidate->instruction() ||
                    candidate->instruction() == instruction ||
                    candidate->instruction()->addr() <= instruction->addr())
                {
                    continue;
                }

                const Dereference *suffixDereference =
                    candidate->left()->asDereference();
                if (!suffixDereference ||
                    suffixDereference->domain() != MemoryDomain::MEMORY ||
                    containsRuntimeMemoryAccess(candidate->right()) ||
                    suffixDereference->size() <= 0 ||
                    suffixDereference->size() % CHAR_BIT != 0 ||
                    suffixDereference->size() >
                        std::numeric_limits<ConstantValue>::digits)
                {
                    continue;
                }

                /*
                 * Only absorb a genuine tail smaller than one REP element.
                 * An equally wide store can intentionally clear the last
                 * array byte together with adjacent scalar locals; treating
                 * that as a larger char array would invent an object boundary.
                 */
                const ConstantValue candidateBytes =
                    suffixDereference->size() / CHAR_BIT;
                if (candidateBytes >= elementBytes) {
                    continue;
                }

                const MemoryLocation &candidateLocation =
                    dataflow_.getMemoryLocation(candidate->left());
                if (!candidateLocation ||
                    candidateLocation.domain() != MemoryDomain::STACK ||
                    candidateLocation.size() != suffixDereference->size() ||
                    candidateLocation.addr() % CHAR_BIT != 0 ||
                    candidateLocation.addr() / CHAR_BIT != repEndOffset)
                {
                    continue;
                }

                ConstantValue candidatePattern;
                if (!concreteValue(candidate->right(), candidatePattern)) {
                    continue;
                }
                bool sameFill = true;
                for (SmallBitSize shift = 0;
                     shift < suffixDereference->size(); shift += CHAR_BIT) {
                    if (((candidatePattern >> shift) & 0xff) != fillByte) {
                        sameFill = false;
                        break;
                    }
                }
                if (!sameFill ||
                    !isDominating(entryStatement, candidate, *dominators_) ||
                    isOnControlFlowCycle(candidate->basicBlock()) ||
                    !hasLinearMemoryFreePathFromExit(candidate))
                {
                    continue;
                }

                if (suffixStore) {
                    suffixStore = nullptr;
                    suffixByteCount = 0;
                    suffixStoreIsAmbiguous = true;
                    break;
                }
                suffixStore = candidate;
                suffixByteCount = candidateBytes;
            }
            if (suffixStoreIsAmbiguous) {
                break;
            }
        }
    }

    if (!suffixStoreIsAmbiguous && suffixStore &&
        suffixByteCount <= (std::numeric_limits<ConstantValue>::max)() - byteCount)
    {
        const ConstantValue extendedByteCount = byteCount + suffixByteCount;
        const auto extendedOffset = getProvenStackOffset(memsetDestination);
        const bool localRangeIsValid =
            extendedOffset && *extendedOffset < 0 &&
            extendedByteCount <=
                static_cast<ConstantValue>(-(*extendedOffset + 1)) + 1;
        if (localRangeIsValid &&
            bitTruncate(extendedByteCount, tree().pointerSize()) ==
                extendedByteCount)
        {
            /* It is normally still ahead in traversal; erase defensively. */
            eraseGeneratedStatement(suffixStore);
            hookStatements_.insert(suffixStore);
            byteCount = extendedByteCount;
        }
    }

    const likec::Type *voidPointerType = tree().makePointerType(tree().pointerSize(), tree().makeVoidType());
    auto functionType = std::make_unique<likec::FunctionPointerType>(tree().pointerSize(), voidPointerType);
    functionType->addArgumentType(voidPointerType);
    functionType->addArgumentType(tree().makeIntegerType(tree().intSize(), false));
    functionType->addArgumentType(tree().makeIntegerType(tree().pointerSize(), true));

    auto call = std::make_unique<likec::CallOperator>(
        std::make_unique<likec::UndeclaredIdentifier>(QLatin1String("memset"), std::move(functionType)));
    if (registerStackBuffer(memsetDestination, byteCount)) {
        auto destination = makeStackBufferAddress(memsetDestination);
        assert(destination != nullptr);
        if (destination) {
            call->addArgument(std::move(destination));
        } else {
            call->addArgument(makeExpressionWithoutStackBuffers(memsetDestination));
        }
    } else {
        call->addArgument(makeExpressionWithoutStackBuffers(memsetDestination));
    }
    call->addArgument(std::make_unique<likec::IntegerConstant>(
        SizedValue(tree().intSize(), fillByte), tree().makeIntegerType(tree().intSize(), false)));
    call->addArgument(std::make_unique<likec::IntegerConstant>(
        SizedValue(tree().pointerSize(), byteCount), tree().makeIntegerType(tree().pointerSize(), true)));

    std::unique_ptr<likec::Statement> result =
        std::make_unique<likec::ExpressionStatement>(std::move(call));
    result->setStatement(memoryWrite);
    return result;
}

boost::optional<SignedConstantValue> DefinitionGenerator::getProvenStackOffset(
        const Term *term) const {
    assert(term != nullptr);

    boost::unordered_set<const Term *> visiting;
    std::function<boost::optional<SignedConstantValue>(const Term *)> recover =
        [&](const Term *current) -> boost::optional<SignedConstantValue> {
            if (!current || !current->isRead() || !visiting.insert(current).second) {
                return boost::none;
            }

            struct EraseOnReturn {
                boost::unordered_set<const Term *> &set;
                const Term *term;
                ~EraseOnReturn() { set.erase(term); }
            } eraseOnReturn{visiting, current};

            if (const Intrinsic *intrinsic = current->as<Intrinsic>()) {
                if (intrinsic->intrinsicKind() == Intrinsic::ZERO_STACK_OFFSET) {
                    return SignedConstantValue(0);
                }
                return boost::none;
            }

            if (const BinaryOperator *binary = current->asBinaryOperator()) {
                auto concreteSignedValue = [&](const Term *operand,
                                               SignedConstantValue &result) {
                    const dflow::Value *value = dataflow_.getValue(operand);
                    if (!value || !value->abstractValue().isConcrete()) {
                        return false;
                    }
                    result = value->abstractValue().asConcrete().signedValue();
                    return true;
                };
                auto checkedAdd = [](SignedConstantValue left,
                                     SignedConstantValue right,
                                     SignedConstantValue &result) {
                    if ((right > 0 && left >
                            (std::numeric_limits<SignedConstantValue>::max)() - right) ||
                        (right < 0 && left <
                            (std::numeric_limits<SignedConstantValue>::min)() - right))
                    {
                        return false;
                    }
                    result = left + right;
                    return true;
                };
                auto checkedSubtract = [](SignedConstantValue left,
                                          SignedConstantValue right,
                                          SignedConstantValue &result) {
                    if ((right > 0 && left <
                            (std::numeric_limits<SignedConstantValue>::min)() + right) ||
                        (right < 0 && left >
                            (std::numeric_limits<SignedConstantValue>::max)() + right))
                    {
                        return false;
                    }
                    result = left - right;
                    return true;
                };

                SignedConstantValue constant;
                SignedConstantValue result;
                if (binary->operatorKind() == BinaryOperator::ADD) {
                    if (auto left = recover(binary->left())) {
                        if (concreteSignedValue(binary->right(), constant) &&
                            checkedAdd(*left, constant, result))
                        {
                            return result;
                        }
                    }
                    if (auto right = recover(binary->right())) {
                        if (concreteSignedValue(binary->left(), constant) &&
                            checkedAdd(*right, constant, result))
                        {
                            return result;
                        }
                    }
                } else if (binary->operatorKind() == BinaryOperator::SUB) {
                    if (auto left = recover(binary->left())) {
                        if (concreteSignedValue(binary->right(), constant) &&
                            checkedSubtract(*left, constant, result))
                        {
                            return result;
                        }
                    }
                }
                return boost::none;
            }

            if (const Term *definition = getTheOnlyDefinition(current, dataflow_)) {
                const MemoryLocation &currentLocation = dataflow_.getMemoryLocation(current);
                const dflow::ReachingDefinitions &definitions =
                    dataflow_.getDefinitions(current);
                if (!currentLocation || definitions.chunks().front().location() != currentLocation) {
                    /* A partial-register definition is not a full pointer copy. */
                    return boost::none;
                }
                return recover(definition->source());
            }
            return boost::none;
        };

    return recover(term);
}

likec::VariableDeclaration *DefinitionGenerator::registerStackBuffer(
        const Term *address, ConstantValue byteCount) {
    assert(address != nullptr);

    const auto provenOffset = getProvenStackOffset(address);
    if (!provenOffset || byteCount < 2 ||
        byteCount > static_cast<ConstantValue>((std::numeric_limits<ByteSize>::max)()) ||
        byteCount > static_cast<ConstantValue>((std::numeric_limits<std::size_t>::max)()))
    {
        return nullptr;
    }

    const SignedConstantValue offset = *provenOffset;
    if (offset >= 0) {
        /* Do not turn arguments or the return-address area into local arrays. */
        return nullptr;
    }

    const ConstantValue availableBeforeFrameBase =
        static_cast<ConstantValue>(-(offset + 1)) + 1;
    if (byteCount > availableBeforeFrameBase) {
        return nullptr;
    }

    const ByteSize size = static_cast<ByteSize>(byteCount);
    const SignedConstantValue endOffset = offset + size;
    foreach (const StackBuffer &buffer, stackBuffers_) {
        const SignedConstantValue bufferEnd = buffer.offset + buffer.size;
        if (buffer.offset == offset && buffer.size == size) {
            return buffer.declaration;
        }
        if (offset < bufferEnd && buffer.offset < endOffset) {
            /* Ambiguous overlapping byte-array views are worse than raw offsets. */
            return nullptr;
        }
    }

    auto declaration = std::make_unique<likec::VariableDeclaration>(
        QString("buffer%1").arg(stackBuffers_.size()),
        tree().makeArrayType(tree().makeIntegerType(CHAR_BIT, false, QString("char")),
                             static_cast<std::size_t>(byteCount)));
    likec::VariableDeclaration *result = declaration.get();
    definition()->block()->addDeclaration(std::move(declaration));
    stackBuffers_.push_back(StackBuffer{offset, size, result});
    return result;
}

std::unique_ptr<likec::Expression> DefinitionGenerator::makeStackBufferAddress(
        const Term *term) {
    assert(term != nullptr);

    if (!term->isRead()) {
        return nullptr;
    }

    auto makeAddress = [&](const StackBuffer &buffer,
                           SignedConstantValue offset,
                           std::unique_ptr<likec::Expression> index)
            -> std::unique_ptr<likec::Expression> {
        assert(buffer.offset <= offset && offset < buffer.offset + buffer.size);

        const ConstantValue displacement =
            static_cast<ConstantValue>(offset - buffer.offset);
        if (index) {
            if (displacement != 0) {
                index = std::make_unique<likec::BinaryOperator>(
                    likec::BinaryOperator::ADD,
                    std::move(index),
                    std::make_unique<likec::IntegerConstant>(
                        SizedValue(tree().pointerSize(), displacement),
                        tree().makeIntegerType(tree().pointerSize(), true)));
            }
        } else if (displacement != 0) {
            index = std::make_unique<likec::IntegerConstant>(
                SizedValue(tree().pointerSize(), displacement),
                tree().makeIntegerType(tree().pointerSize(), true));
        }

        auto identifier =
            std::make_unique<likec::VariableIdentifier>(buffer.declaration);
        if (!index) {
            return identifier;
        }

        auto element = std::make_unique<likec::BinaryOperator>(
            likec::BinaryOperator::ARRAY_SUBSCRIPT,
            std::move(identifier),
            std::move(index));
        return std::make_unique<likec::UnaryOperator>(
            likec::UnaryOperator::REFERENCE, std::move(element));
    };

    if (const auto provenOffset = getProvenStackOffset(term)) {
        foreach (const StackBuffer &buffer, stackBuffers_) {
            const SignedConstantValue endOffset = buffer.offset + buffer.size;
            if (*provenOffset >= buffer.offset && *provenOffset < endOffset) {
                return makeAddress(buffer, *provenOffset, nullptr);
            }
        }
        return nullptr;
    }

    /*
     * Preserve a non-constant byte index in expressions such as
     *
     *     zero_stack_offset - 0x12c + i
     *
     * Once the fixed part identifies a registered char array, this is exactly
     * &buffer[i].  Dynamic subtraction is deliberately rejected; accepting
     * only additive indices keeps the rewrite both simple and exact.
     */
    struct AdditivePart {
        const Term *term;
        bool subtract;
    };
    std::vector<AdditivePart> parts;
    std::function<void(const Term *, bool)> collect =
        [&](const Term *current, bool subtract) {
            if (const BinaryOperator *binary = current->asBinaryOperator()) {
                if (binary->operatorKind() == BinaryOperator::ADD) {
                    collect(binary->left(), subtract);
                    collect(binary->right(), subtract);
                    return;
                }
                if (binary->operatorKind() == BinaryOperator::SUB) {
                    collect(binary->left(), subtract);
                    collect(binary->right(), !subtract);
                    return;
                }
            }
            parts.push_back(AdditivePart{current, subtract});
        };
    collect(term, false);

    bool haveStackBase = false;
    SignedConstantValue fixedOffset = 0;
    std::vector<const Term *> dynamicParts;

    auto checkedAdd = [](SignedConstantValue left, SignedConstantValue right,
                         SignedConstantValue &result) {
        if ((right > 0 && left >
                (std::numeric_limits<SignedConstantValue>::max)() - right) ||
            (right < 0 && left <
                (std::numeric_limits<SignedConstantValue>::min)() - right))
        {
            return false;
        }
        result = left + right;
        return true;
    };
    auto checkedSubtract = [](SignedConstantValue left, SignedConstantValue right,
                              SignedConstantValue &result) {
        if ((right > 0 && left <
                (std::numeric_limits<SignedConstantValue>::min)() + right) ||
            (right < 0 && left >
                (std::numeric_limits<SignedConstantValue>::max)() + right))
        {
            return false;
        }
        result = left - right;
        return true;
    };

    foreach (const AdditivePart &part, parts) {
        if (const auto stackOffset = getProvenStackOffset(part.term)) {
            if (part.subtract || haveStackBase ||
                !checkedAdd(fixedOffset, *stackOffset, fixedOffset))
            {
                return nullptr;
            }
            haveStackBase = true;
            continue;
        }

        const dflow::Value *value = dataflow_.getValue(part.term);
        if (value && value->abstractValue().isConcrete()) {
            const SignedConstantValue constant =
                value->abstractValue().asConcrete().signedValue();
            const bool valid = part.subtract ?
                checkedSubtract(fixedOffset, constant, fixedOffset) :
                checkedAdd(fixedOffset, constant, fixedOffset);
            if (!valid) {
                return nullptr;
            }
            continue;
        }

        if (part.subtract) {
            return nullptr;
        }
        dynamicParts.push_back(part.term);
    }

    if (!haveStackBase || dynamicParts.empty()) {
        return nullptr;
    }

    const StackBuffer *selectedBuffer = nullptr;
    foreach (const StackBuffer &buffer, stackBuffers_) {
        const SignedConstantValue endOffset = buffer.offset + buffer.size;
        if (fixedOffset >= buffer.offset && fixedOffset < endOffset) {
            selectedBuffer = &buffer;
            break;
        }
    }
    if (!selectedBuffer) {
        return nullptr;
    }

    std::unique_ptr<likec::Expression> index;
    foreach (const Term *part, dynamicParts) {
        auto expression = makeExpressionWithoutStackBuffers(part);
        if (!index) {
            index = std::move(expression);
        } else {
            index = std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::ADD, std::move(index), std::move(expression));
        }
    }
    return makeAddress(*selectedBuffer, fixedOffset, std::move(index));
}

std::unique_ptr<likec::Expression>
DefinitionGenerator::makeExpressionWithoutStackBuffers(const Term *term) {
    struct FlagRestorer {
        bool &flag;
        bool oldValue;
        ~FlagRestorer() { flag = oldValue; }
    } restorer{suppressStackBufferExpressions_, suppressStackBufferExpressions_};

    suppressStackBufferExpressions_ = true;
    return makeExpression(term);
}

std::unique_ptr<likec::Statement> DefinitionGenerator::makeRepneScasLength(
        const cflow::Region *region) {
    assert(region != nullptr);

    /*
     * SCAS is expanded into a synthetic loop by X86InstructionAnalyzer.  A
     * source-level strlen is only equivalent to one particularly common use
     * of that loop, so deliberately recognize the whole idiom instead of
     * replacing arbitrary SCAS instructions.
     */
    std::vector<const Statement *> statements;
    std::function<void(const cflow::Node *)> collectStatements =
        [&](const cflow::Node *node) {
            if (auto basicNode = node->as<cflow::BasicNode>()) {
                foreach (const Statement *statement, basicNode->basicBlock()->statements()) {
                    statements.push_back(statement);
                }
            } else if (auto nestedRegion = node->as<cflow::Region>()) {
                foreach (const cflow::Node *nestedNode, nestedRegion->nodes()) {
                    collectStatements(nestedNode);
                }
            }
        };
    collectStatements(region);

    const arch::Instruction *instruction = nullptr;
    foreach (const Statement *statement, statements) {
        if (!statement->instruction()) {
            /* Replacing the region must not silently discard hook semantics. */
            return nullptr;
        }
        if (!instruction) {
            instruction = statement->instruction();
        } else if (statement->instruction() != instruction) {
            return nullptr;
        }
        if (!statement->asAssignment() && !statement->asJump()) {
            return nullptr;
        }
    }
    if (!instruction) {
        return nullptr;
    }

    const QString instructionText = instruction->toString().trimmed().toLower();
    if (!(instructionText.startsWith(QLatin1String("repne ")) ||
          instructionText.startsWith(QLatin1String("repnz "))) ||
        !instructionText.contains(QLatin1String("scasb")))
    {
        return nullptr;
    }

    auto sameLocation = [&](const Term *left, const Term *right) {
        const MemoryLocation &leftLocation = dataflow_.getMemoryLocation(left);
        return leftLocation && leftLocation == dataflow_.getMemoryLocation(right);
    };
    auto concreteValue = [&](const Term *term, ConstantValue &result) {
        const dflow::Value *value = dataflow_.getValue(term);
        if (!value || !value->abstractValue().isConcrete()) {
            return false;
        }
        result = value->abstractValue().asConcrete().value();
        return true;
    };

    const Assignment *countUpdate = nullptr;
    const Assignment *destinationUpdate = nullptr;
    const Assignment *zeroFlagUpdate = nullptr;
    const Term *countRead = nullptr;
    const Term *destinationRead = nullptr;
    const Term *accumulatorRead = nullptr;
    const Dereference *scannedByte = nullptr;

    foreach (const Statement *statement, statements) {
        if (statement->instruction() != instruction) {
            continue;
        }

        const Assignment *assignment = statement->asAssignment();
        if (!assignment) {
            continue;
        }

        const BinaryOperator *binary = assignment->right()->asBinaryOperator();
        if (!binary) {
            continue;
        }

        ConstantValue delta;
        if (sameLocation(assignment->left(), binary->left()) &&
            concreteValue(binary->right(), delta))
        {
            if (binary->operatorKind() == BinaryOperator::SUB && delta == 1) {
                if (countUpdate) {
                    return nullptr;
                }
                countUpdate = assignment;
                countRead = binary->left();
                continue;
            }
            if (binary->operatorKind() == BinaryOperator::ADD && delta == 1) {
                if (destinationUpdate) {
                    return nullptr;
                }
                destinationUpdate = assignment;
                destinationRead = binary->left();
                continue;
            }
        }

        if (binary->operatorKind() == BinaryOperator::EQUAL) {
            const Dereference *candidate = binary->left()->asDereference();
            const Term *accumulator = binary->right();
            if (!candidate) {
                candidate = binary->right()->asDereference();
                accumulator = binary->left();
            }
            if (candidate && candidate->domain() == MemoryDomain::MEMORY &&
                candidate->size() == CHAR_BIT)
            {
                if (zeroFlagUpdate) {
                    return nullptr;
                }
                zeroFlagUpdate = assignment;
                scannedByte = candidate;
                accumulatorRead = accumulator;
            }
        }
    }

    if (!countUpdate || !destinationUpdate || !zeroFlagUpdate ||
        !countRead || !destinationRead || !accumulatorRead || !scannedByte ||
        !sameLocation(scannedByte->address(), destinationRead))
    {
        return nullptr;
    }

    /* A +1 destination update proves that DF was clear for this SCASB. */
    const BinaryOperator *destinationExpression =
        destinationUpdate->right()->asBinaryOperator();
    ConstantValue destinationDelta;
    if (!destinationExpression ||
        !concreteValue(destinationExpression->right(), destinationDelta) ||
        destinationDelta != 1)
    {
        return nullptr;
    }

    auto initialSource = [&](const Term *read) -> const Term * {
        if (!read || !read->isRead()) {
            return nullptr;
        }

        const Term *result = nullptr;
        const dflow::ReachingDefinitions &definitions = dataflow_.getDefinitions(read);
        const MemoryLocation &readLocation = dataflow_.getMemoryLocation(read);
        if (!readLocation || definitions.chunks().empty()) {
            return nullptr;
        }

        BitAddr nextAddress = readLocation.addr();
        foreach (const dflow::ReachingDefinitions::Chunk &chunk, definitions.chunks()) {
            if (chunk.location().domain() != readLocation.domain() ||
                chunk.location().addr() != nextAddress ||
                chunk.hasUnknownDefinition())
            {
                return nullptr;
            }
            nextAddress = chunk.location().endAddr();
            foreach (const Term *definition, chunk.definitions()) {
                const Statement *sourceStatement = definition->statement();
                if (sourceStatement && sourceStatement->instruction() == instruction) {
                    continue;
                }
                if (!definition->source() || (result && result != definition->source())) {
                    return nullptr;
                }
                result = definition->source();
            }
        }
        if (nextAddress != readLocation.endAddr()) {
            return nullptr;
        }
        return result;
    };

    const Term *initialCount = initialSource(countRead);
    const Term *initialDestination = initialSource(destinationRead);
    ConstantValue count;
    ConstantValue accumulator;
    if (!initialCount || !initialDestination ||
        !concreteValue(initialCount, count) ||
        count != bitMask<ConstantValue>(countRead->size()) ||
        !concreteValue(accumulatorRead, accumulator) || accumulator != 0)
    {
        return nullptr;
    }

    auto externalLiveUses = [&](const Term *write) {
        std::vector<const Term *> result;
        foreach (const dflow::Uses::Use &use, uses_->getUses(write)) {
            if (!liveness_.isLive(use.term())) {
                continue;
            }
            const Statement *useStatement = use.term()->statement();
            if (useStatement && useStatement->instruction() == instruction) {
                continue;
            }
            if (std::find(result.begin(), result.end(), use.term()) == result.end()) {
                result.push_back(use.term());
            }
        }
        return result;
    };

    /*
     * The final destination and all comparison flags must be dead.  Only the
     * loop-carried count may escape, and only into the canonical NOT/DEC
     * length materialization below.
     */
    foreach (const Statement *statement, statements) {
        if (statement->instruction() != instruction) {
            continue;
        }
        const Assignment *assignment = statement->asAssignment();
        if (assignment && assignment != countUpdate &&
            !externalLiveUses(assignment->left()).empty())
        {
            return nullptr;
        }
    }

    const std::vector<const Term *> countUses = externalLiveUses(countUpdate->left());
    if (countUses.size() != 1) {
        return nullptr;
    }

    const Assignment *notAssignment = countUses.front()->statement() ?
        countUses.front()->statement()->asAssignment() : nullptr;
    const UnaryOperator *notExpression = notAssignment ?
        notAssignment->right()->asUnaryOperator() : nullptr;
    if (!notAssignment || !notExpression ||
        notExpression->operatorKind() != UnaryOperator::NOT ||
        notExpression->operand() != countUses.front() ||
        !sameLocation(notAssignment->left(), countUpdate->left()))
    {
        return nullptr;
    }

    const std::vector<const Term *> notUses = externalLiveUses(notAssignment->left());
    if (notUses.size() != 1) {
        return nullptr;
    }

    const Assignment *decrementAssignment = notUses.front()->statement() ?
        notUses.front()->statement()->asAssignment() : nullptr;
    const BinaryOperator *decrementExpression = decrementAssignment ?
        decrementAssignment->right()->asBinaryOperator() : nullptr;
    ConstantValue decrement;
    if (!decrementAssignment || !decrementExpression ||
        decrementExpression->operatorKind() != BinaryOperator::SUB ||
        decrementExpression->left() != notUses.front() ||
        !concreteValue(decrementExpression->right(), decrement) || decrement != 1 ||
        !sameLocation(decrementAssignment->left(), notAssignment->left()) ||
        !liveness_.isLive(decrementAssignment->left()))
    {
        return nullptr;
    }

    /*
     * Keep the final architectural value as a real assignment.  Marking the
     * two scalar bookkeeping assignments as hooks prevents source-expression
     * substitution from resurrecting the NOT/DEC sequence at later uses.
     */
    hookStatements_.insert(notAssignment);
    hookStatements_.insert(decrementAssignment);
    isSubstituted_.erase(notAssignment->left());
    isSubstituted_.erase(decrementAssignment->left());

    const likec::Type *returnType =
        tree().makeIntegerType(tree().pointerSize(), true);
    const likec::Type *characterType = tree().makeIntegerType(CHAR_BIT, false);
    const likec::Type *characterPointerType =
        tree().makePointerType(tree().pointerSize(), characterType);
    auto functionType =
        std::make_unique<likec::FunctionPointerType>(tree().pointerSize(), returnType);
    functionType->addArgumentType(characterPointerType);

    auto call = std::make_unique<likec::CallOperator>(
        std::make_unique<likec::UndeclaredIdentifier>(
            QLatin1String("strlen"), std::move(functionType)));
    call->addArgument(makeExpression(initialDestination));

    std::unique_ptr<likec::Statement> result =
        std::make_unique<likec::ExpressionStatement>(
            std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::ASSIGN,
                makeExpression(decrementAssignment->left()),
                std::make_unique<likec::Typecast>(
                    likec::Typecast::C_STYLE_CAST,
                    parent().makeType(parent().types().getType(
                        decrementAssignment->left())),
                    std::move(call))));
    result->setStatement(countUpdate);
    return result;
}

std::unique_ptr<likec::Statement> DefinitionGenerator::makeJump(const BasicBlock *target, const BasicBlock *nextBB,
                                                                const BasicBlock *breakBB,
                                                                const BasicBlock *continueBB) {
    if (target == nextBB) {
        return nullptr;
    } else if (target == breakBB) {
        return std::make_unique<likec::Break>();
    } else if (target == continueBB) {
        return std::make_unique<likec::Continue>();
    } else {
        return std::make_unique<likec::Goto>(
                std::make_unique<likec::LabelIdentifier>(makeLabel(target)));
    }
}

std::unique_ptr<likec::Statement> DefinitionGenerator::makeJump(const Jump *jump, const JumpTarget &target,
                                                                const BasicBlock *nextBB, const BasicBlock *breakBB,
                                                                const BasicBlock *continueBB) {
    assert(jump != nullptr);

    if (target.basicBlock()) {
        return makeJump(target.basicBlock(), nextBB, breakBB, continueBB);
    } else if (target.address()) {
        if (dflow::isReturnAddress(target.address(), dataflow_)) {
            if (signature()->returnValue()) {
                if (auto returnHook = parent().hooks().getReturnHook(jump)) {
                    return std::make_unique<likec::Return>(
                        makeExpression(returnHook->getReturnValueTerm(signature()->returnValue().get())));
                }
            }
            return std::make_unique<likec::Return>();
        }
        return std::make_unique<likec::Goto>(makeExpression(target.address()));
    } else {
        return std::make_unique<likec::Goto>(std::make_unique<likec::String>(QLatin1String("???")));
    }
}

std::unique_ptr<likec::Expression> DefinitionGenerator::makeExpression(const Term *term) {
    assert(term != nullptr);

    auto result = doMakeExpression(term);
    assert(result != nullptr);

    class TermSetter {
        const ir::Term *term_;

    public:
        TermSetter(const ir::Term *term): term_(term) {
            assert(term != nullptr);
        }

        void operator()(likec::TreeNode *node) {
            if (auto expression = node->as<likec::Expression>()) {
                if (expression->term() == nullptr) {
                    expression->setTerm(term_);
                    expression->callOnChildren(*this);
                }
            }
        }
    };

    TermSetter setter(term);
    setter(result.get());

    return result;
}

std::unique_ptr<likec::Expression> DefinitionGenerator::doMakeExpression(const Term *term) {
#ifdef NC_PREFER_CONSTANTS_TO_EXPRESSIONS
    if (term->isRead()) {
        const dflow::Value *value = dataflow_.getValue(term);

        if (value->abstractValue().isConcrete()) {
            return makeConstant(term, value->abstractValue().asConcrete());
        }
    }
#endif

    if (!suppressStackBufferExpressions_) {
        if (auto stackBufferAddress = makeStackBufferAddress(term)) {
            return stackBufferAddress;
        }

        /* Keep accesses inside a proven byte array tied to that declaration. */
        if (const Dereference *dereference = term->asDereference()) {
            if (dereference->size() == CHAR_BIT) {
                if (auto address = makeStackBufferAddress(dereference->address())) {
                    return std::make_unique<likec::UnaryOperator>(
                        likec::UnaryOperator::DEREFERENCE, std::move(address));
                }
            } else if (dereference->size() > 0 &&
                       dereference->size() % CHAR_BIT == 0) {
                const auto offset = getProvenStackOffset(dereference->address());
                const ByteSize byteCount = dereference->size() / CHAR_BIT;
                if (offset) {
                    foreach (const StackBuffer &buffer, stackBuffers_) {
                        const SignedConstantValue endOffset = buffer.offset + buffer.size;
                        if (*offset < buffer.offset || *offset >= endOffset ||
                            byteCount > buffer.size ||
                            *offset > endOffset - static_cast<SignedConstantValue>(byteCount))
                        {
                            continue;
                        }

                        auto address = makeStackBufferAddress(dereference->address());
                        if (!address) {
                            break;
                        }
                        const types::Type *type = parent().types().getType(dereference);
                        const types::Type *addressType =
                            parent().types().getType(dereference->address());
                        return std::make_unique<likec::UnaryOperator>(
                            likec::UnaryOperator::DEREFERENCE,
                            std::make_unique<likec::Typecast>(
                                likec::Typecast::C_STYLE_CAST,
                                tree().makePointerType(
                                    addressType->size(), parent().makeType(type)),
                                std::move(address)));
                    }
                }
            }
        }
    }

    if (term->isRead()) {
        if (const Term *substitute = getSubstitute(term)) {
            return makeExpression(substitute);
        }
    }

    if (parent().variables().getVariable(term)) {
        return makeVariableAccess(term);
    }

    switch (term->kind()) {
        case Term::INT_CONST: {
            return makeConstant(term, term->asConstant()->value());
        }
        case Term::INTRINSIC: {
            return doMakeExpression(term->as<Intrinsic>());
        }
        case Term::MEMORY_LOCATION_ACCESS: {
            assert(!"The term must belong to a variable.");
            return nullptr;
        }
        case Term::DEREFERENCE: {
            assert(!dataflow_.getMemoryLocation(term) && "The term must belong to a variable.");

            auto dereference = term->asDereference();
            auto type = parent().types().getType(dereference);
            auto addressType = parent().types().getType(dereference->address());

            return std::make_unique<likec::UnaryOperator>(likec::UnaryOperator::DEREFERENCE,
                std::make_unique<likec::Typecast>(
                    likec::Typecast::C_STYLE_CAST,
                    tree().makePointerType(addressType->size(), parent().makeType(type)),
                    makeExpression(dereference->address())));
        }
        case Term::UNARY_OPERATOR: {
            return doMakeExpression(term->asUnaryOperator());
        }
        case Term::BINARY_OPERATOR: {
            return doMakeExpression(term->asBinaryOperator());
        }
        default: {
            unreachable();
            return nullptr;
        }
    }
}

std::unique_ptr<likec::Expression> DefinitionGenerator::doMakeExpression(const UnaryOperator *unary) {
    std::unique_ptr<likec::Expression> operand(makeExpression(unary->operand()));

    switch (unary->operatorKind()) {
        case UnaryOperator::NOT: {
            const types::Type *operandType = parent().types().getType(unary->operand());
            return std::make_unique<likec::UnaryOperator>(
                likec::UnaryOperator::BITWISE_NOT,
                std::make_unique<likec::Typecast>(
                    likec::Typecast::C_STYLE_CAST,
                    tree().makeIntegerType(operandType->size(), operandType->isUnsigned()), std::move(operand)));
        }
        case UnaryOperator::NEGATION: {
            const types::Type *operandType = parent().types().getType(unary->operand());
            return std::make_unique<likec::UnaryOperator>(
                likec::UnaryOperator::NEGATION,
                std::make_unique<likec::Typecast>(
                    likec::Typecast::C_STYLE_CAST,
                    tree().makeIntegerType(operandType->size(), operandType->isUnsigned()), std::move(operand)));
        }
        case UnaryOperator::SIGN_EXTEND: {
            return std::make_unique<likec::Typecast>(
                likec::Typecast::STATIC_CAST, tree().makeIntegerType(unary->size(), false),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(unary->operand()->size(), false),
                                                  std::move(operand)));
        }
        case UnaryOperator::ZERO_EXTEND: {
            return std::make_unique<likec::Typecast>(
                likec::Typecast::STATIC_CAST, tree().makeIntegerType(unary->size(), true),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(unary->operand()->size(), true),
                                                  std::move(operand)));
        }
        case UnaryOperator::TRUNCATE: {
            const types::Type *type = parent().types().getType(unary);
            const types::Type *operandType = parent().types().getType(unary->operand());
            return std::make_unique<likec::Typecast>(
                likec::Typecast::STATIC_CAST, tree().makeIntegerType(unary->size(), type->isUnsigned()),
                std::make_unique<likec::Typecast>(
                    likec::Typecast::C_STYLE_CAST,
                    tree().makeIntegerType(unary->operand()->size(), operandType->isUnsigned()), std::move(operand)));
        }
        default:
            unreachable();
    }
}

std::unique_ptr<likec::Expression> DefinitionGenerator::doMakeExpression(const BinaryOperator *binary) {
    const types::Type *leftType = parent().types().getType(binary->left());
    const types::Type *rightType = parent().types().getType(binary->right());

    std::unique_ptr<likec::Expression> left(makeExpression(binary->left()));
    std::unique_ptr<likec::Expression> right(makeExpression(binary->right()));

    switch (binary->operatorKind()) {
        case BinaryOperator::AND:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::BITWISE_AND,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::OR:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::BITWISE_OR,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::XOR:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::BITWISE_XOR,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::SHL:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::SHL,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::SHR:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::SHR,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), true), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::SAR:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::SHR,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), false), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::ADD:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::ADD,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::SUB:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::SUB,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::MUL:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::MUL,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), leftType->isUnsigned()),
                                                  std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), rightType->isUnsigned()),
                                                  std::move(right)));

        case BinaryOperator::SIGNED_DIV:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::DIV,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), false), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), false), std::move(right)));

        case BinaryOperator::SIGNED_REM:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::REM,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), false), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), false), std::move(right)));

        case BinaryOperator::UNSIGNED_DIV:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::DIV,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), true), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), true), std::move(right)));

        case BinaryOperator::UNSIGNED_REM:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::REM,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), true), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), true), std::move(right)));

        case BinaryOperator::EQUAL:
            return std::make_unique<likec::BinaryOperator>(likec::BinaryOperator::EQ,
                std::move(left),
                std::move(right));

        case BinaryOperator::SIGNED_LESS:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::LT,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), false), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), false), std::move(right)));

        case BinaryOperator::SIGNED_LESS_OR_EQUAL:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::LEQ,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), false), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), false), std::move(right)));

        case BinaryOperator::UNSIGNED_LESS:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::LT,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), true), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), true), std::move(right)));

        case BinaryOperator::UNSIGNED_LESS_OR_EQUAL:
            return std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::LEQ,
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(leftType->size(), true), std::move(left)),
                std::make_unique<likec::Typecast>(likec::Typecast::C_STYLE_CAST,
                                                  tree().makeIntegerType(rightType->size(), true), std::move(right)));

        default:
            unreachable();
            return nullptr;
    }
}

std::unique_ptr<likec::Expression> DefinitionGenerator::doMakeExpression(const Intrinsic *intrinsic) {
    switch (intrinsic->intrinsicKind()) {
        case Intrinsic::UNDEFINED:
            return makeIntrinsicCall(
                QLatin1String("__undefined"),
                parent().makeType(parent().types().getType(intrinsic)));
        case Intrinsic::ZERO_STACK_OFFSET:
            return makeIntrinsicCall(
                QLatin1String("__zero_stack_offset"),
                parent().tree().makePointerType(parent().tree().pointerSize(), parent().tree().makeVoidType()));
        case Intrinsic::RETURN_ADDRESS:
            return makeIntrinsicCall(
                QLatin1String("__return_address"),
                parent().tree().makePointerType(parent().tree().pointerSize(), parent().tree().makeVoidType()));
    }
    return makeIntrinsicCall(QLatin1String("__intrinsic"), parent().makeType(parent().types().getType(intrinsic)));
}

std::unique_ptr<likec::Expression> DefinitionGenerator::makeIntrinsicCall(QLatin1String name,
                                                                          const likec::Type *returnType) {
    return std::make_unique<likec::CallOperator>(std::make_unique<likec::UndeclaredIdentifier>(
        name, std::make_unique<likec::FunctionPointerType>(parent().tree().pointerSize(), returnType)));
}

std::unique_ptr<likec::Expression> DefinitionGenerator::makeConstant(const Term *term, const SizedValue &value) {
    const types::Type *type = parent().types().getType(term);

#ifdef NC_PREFER_FUNCTIONS_TO_CONSTANTS
    if (auto section = parent().image().getSectionContainingAddress(value.value())) {
        if (section->isCode()) {
            if (auto functionDeclaration = parent().makeFunctionDeclaration(value.value())) {
                return std::make_unique<likec::FunctionIdentifier>(functionDeclaration);
            }
        }
    }
#endif

#ifdef NC_PREFER_CSTRINGS_TO_CONSTANTS
    {
        auto isAscii = [](const QString &string) -> bool {
            foreach (QChar c, string) {
                if (c >= 0x80 || (c < 0x20 && c != '\r' && c != '\n' && c != '\t')) {
                    return false;
                }
            }
            return true;
        };

        QString string = image::Reader(&parent().image()).readAsciizString(value.value(), 1024);

        if (!string.isEmpty() && isAscii(string)) {
            return std::make_unique<likec::String>(string);
        }
    }
#endif

#ifdef NC_PREFER_GLOBAL_VARIABLES_TO_CONSTANTS
    if (type->pointee() && type->pointee()->size()) {
        return std::make_unique<likec::UnaryOperator>(
            likec::UnaryOperator::REFERENCE,
            std::make_unique<likec::VariableIdentifier>(
                parent().makeGlobalVariableDeclaration(
                    MemoryLocation(MemoryDomain::MEMORY, value.value() * CHAR_BIT, type->pointee()->size()),
                    type)));
    }
#endif

    return std::make_unique<likec::IntegerConstant>(value, tree().makeIntegerType(value.size(), type->isUnsigned()));
}

std::unique_ptr<likec::Expression> DefinitionGenerator::makeVariableAccess(const Term *term) {
    assert(term != nullptr);

    const auto &termLocation = dataflow_.getMemoryLocation(term);
    assert(termLocation);

    auto variable = parent().variables().getVariable(term);
    assert(variable != nullptr);

    auto identifier = std::make_unique<likec::VariableIdentifier>(makeVariableDeclaration(variable));

    if (termLocation == variable->memoryLocation()) {
        return std::move(identifier);
    } else {
        /*
         * Generate pointer arithmetics to get to the right part of the variable.
         *
         * Note: this does not handle the case of non-byte-aligned locations.
         * However, I am not sure whether they can be reliably handled in C at all.
         */
        auto variableAddress = std::make_unique<likec::Typecast>(
            likec::Typecast::C_STYLE_CAST,
            tree().makeIntegerType(tree().pointerSize(), false),
            std::make_unique<likec::UnaryOperator>(
                likec::UnaryOperator::REFERENCE,
                std::move(identifier)));

        std::unique_ptr<likec::Expression> termAddress;
        if (termLocation.addr() == variable->memoryLocation().addr()) {
            termAddress = std::move(variableAddress);
        } else {
            termAddress = std::make_unique<likec::BinaryOperator>(
                likec::BinaryOperator::ADD,
                std::move(variableAddress),
                std::make_unique<likec::IntegerConstant>(
                    (termLocation.addr() - variable->memoryLocation().addr()) / CHAR_BIT,
                    tree().makeIntegerType(tree().pointerSize(), false)));
        }

        return std::make_unique<likec::UnaryOperator>(
            likec::UnaryOperator::DEREFERENCE,
            std::make_unique<likec::Typecast>(
                likec::Typecast::C_STYLE_CAST,
                tree().makePointerType(parent().makeType(parent().types().getType(term))),
                std::move(termAddress)));
    }
}

const Term *DefinitionGenerator::getSubstitute(const Term *read) {
    assert(read != nullptr);
    assert(read->isRead());
    assert(liveness_.isLive(read));

    if (auto write = getTheOnlyDefinition(read, dataflow_)) {
        if (isSubstituted(write)) {
            return write->source();
        }
    }
    return nullptr;
}

bool DefinitionGenerator::isSubstituted(const Term *write) {
    assert(write != nullptr);
    assert(write->isWrite());
    assert(liveness_.isLive(write));

    auto i = isSubstituted_.find(write);
    if (i != isSubstituted_.end()) {
        /* The result is being computed? */
        if (i->second == boost::none) {
            /* Cyclic dependency. */
            i->second = false;
        }
        return *i->second;
    }

    /* Mark the result as being computed. */
    isSubstituted_.emplace_hint(i, std::make_pair(write, boost::none));

    auto result = computeIsSubstituted(write);

    auto &cached = isSubstituted_[write];
    if (!cached) {
        cached = result;
    }

    return result;
}

bool DefinitionGenerator::computeIsSubstituted(const Term *write) {
    auto source = write->source();
    if (!source) {
        return false;
    }

    if (nc::contains(hookStatements_, write->statement())) {
        return false;
    }

    const auto &memoryLocation = dataflow_.getMemoryLocation(write);
    if (!memoryLocation) {
        return false;
    }

    if (!parent().variables().getVariable(write)->isLocal()) {
        return false;
    }

    std::size_t nuses = 0;

    foreach (const auto &use, uses_->getUses(write)) {
        auto read = use.term();

        if (liveness_.isLive(read)) {
            if (dataflow_.getMemoryLocation(read) != memoryLocation) {
                return false;
            }

            auto theOnlyDefinition = getTheOnlyDefinition(read, dataflow_);
            if (!theOnlyDefinition) {
                return false;
            }
            assert(theOnlyDefinition == write);

            if (!isDominating(write->statement(), read->statement(), *dominators_)) {
                return false;
            }

            if (!canBeMoved(source, read->statement())) {
                return false;
            }

            ++nuses;
        }
    }

    assert(nuses >= 1 && "Live write must have at least one live read.");

    if (nuses > 1) {
        auto sourceSubstitute = getSubstitute(source);
        if (!sourceSubstitute) {
            sourceSubstitute = source;
        }
        if (sourceSubstitute->kind() == Term::UNARY_OPERATOR || sourceSubstitute->kind() == Term::BINARY_OPERATOR) {
            /* We do not want to substitute complex expressions multiple times. */
            return false;
        }
    }

    return true;
}

bool DefinitionGenerator::canBeMoved(const Term *term, const Statement *destination) {
    assert(term != nullptr);
    assert(term->isRead());
    assert(destination != nullptr);
    assert(liveness_.isLive(term));

#ifdef NC_PREFER_CONSTANTS_TO_EXPRESSIONS
    if (dataflow_.getValue(term)->abstractValue().isConcrete()) {
        return true;
    }
#endif

    if (auto substitute = getSubstitute(term)) {
        return canBeMoved(substitute, destination);
    }

    switch (term->kind()) {
        case Term::INT_CONST:
        case Term::INTRINSIC: {
            return true;
        }
        case Term::MEMORY_LOCATION_ACCESS:
        case Term::DEREFERENCE: {
            if (auto variable = parent().variables().getVariable(term)) {
                /*
                 * This assumes that our dataflow analysis has successfully
                 * detected all accesses to the local variable, which obviously
                 * cannot always be the case.
                 */
                return variable->isLocal() &&
                     allOfStatementsBetween(
                        term->statement(), destination, *cfg_,
                        [&](const Statement *statement) -> bool {
                            auto term = getWrittenTerm(statement);
                            return !term || parent().variables().getVariable(term) != variable;
                        }) == true;
            }

            Domain domain = *getDomain(term);
            return allOfStatementsBetween(
                term->statement(), destination, *cfg_,
                [&](const Statement *statement) -> bool {
                    auto term = getWrittenTerm(statement);
                    return !term || getDomain(term) != domain;
                }) == true;
        }
        case Term::UNARY_OPERATOR: {
            auto unary = term->asUnaryOperator();
            return canBeMoved(unary->operand(), destination);
        }
        case Term::BINARY_OPERATOR: {
            auto binary = term->asBinaryOperator();
            return canBeMoved(binary->left(), destination) &&
                   canBeMoved(binary->right(), destination);
        }
    }
    unreachable();
}

} // namespace cgen
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
