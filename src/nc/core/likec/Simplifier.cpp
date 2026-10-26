#include "Simplifier.h"

#include <algorithm>

#include <nc/common/Foreach.h>
#include <nc/common/Unreachable.h>
#include <nc/common/make_unique.h>

#include "BinaryOperator.h"
#include "Break.h"
#include "CallOperator.h"
#include "CaseLabel.h"
#include "CompilationUnit.h"
#include "Declaration.h"
#include "DefaultLabel.h"
#include "DoWhile.h"
#include "Expression.h"
#include "ExpressionStatement.h"
#include "For.h"
#include "FunctionDefinition.h"
#include "Goto.h"
#include "If.h"
#include "IntegerConstant.h"
#include "LabelStatement.h"
#include "MemberAccessOperator.h"
#include "Return.h"
#include "Statement.h"
#include "StructType.h"
#include "Switch.h"
#include "Tree.h"
#include "Typecast.h"
#include "Types.h"
#include "UnaryOperator.h"
#include "UndeclaredIdentifier.h"
#include "Utils.h"
#include "VariableDeclaration.h"
#include "VariableIdentifier.h"
#include "While.h"

namespace nc {
namespace core {
namespace likec {

namespace {

struct IsNull {
    template<class T>
    bool operator()(const T& item) const {
        return !item;
    }
};

template<class T, class U>
std::unique_ptr<T> as(std::unique_ptr<U> ptr) {
    assert(ptr);
    auto result = std::unique_ptr<T>(ptr.release()->template as<T>());
    assert(result);
    return result;
}

struct SwitchCase {
    If *conditional;
    bool variableIsLeftOperand;
    std::unique_ptr<Statement> *statement;
    SizedValue value;
};

struct SwitchComparison {
    const VariableDeclaration *variable;
    bool isEquality;
    bool variableIsLeftOperand;
    IntegerConstant *constant;
};

VariableIdentifier *getSwitchVariable(Expression *expression) {
    const Type *castType = nullptr;
    while (auto typecast = expression->as<Typecast>()) {
        if (!typecast->type()->isInteger() ||
            (castType && castType->size() != typecast->type()->size())) {
            return nullptr;
        }
        castType = typecast->type();
        expression = typecast->operand().get();
    }

    auto variable = expression->as<VariableIdentifier>();
    if (!variable || !variable->declaration()->type()->isInteger() ||
        (castType && castType->size() != variable->declaration()->type()->size())) {
        return nullptr;
    }
    return variable;
}

bool getSwitchComparison(If *conditional, SwitchComparison &result) {
    auto binary = conditional->condition()->as<BinaryOperator>();
    if (!binary || (binary->operatorKind() != BinaryOperator::EQ &&
                    binary->operatorKind() != BinaryOperator::NEQ)) {
        return false;
    }

    auto leftVariable = getSwitchVariable(binary->left().get());
    auto rightVariable = getSwitchVariable(binary->right().get());
    auto leftConstant = binary->left()->as<IntegerConstant>();
    auto rightConstant = binary->right()->as<IntegerConstant>();

    if (leftVariable && rightConstant) {
        result.variable = leftVariable->declaration();
        result.variableIsLeftOperand = true;
        result.constant = rightConstant;
    } else if (rightVariable && leftConstant) {
        result.variable = rightVariable->declaration();
        result.variableIsLeftOperand = false;
        result.constant = leftConstant;
    } else {
        return false;
    }

    result.isEquality = binary->operatorKind() == BinaryOperator::EQ;
    return true;
}

If *getNestedIf(Statement *statement, bool &invalidWrapper) {
    invalidWrapper = false;

    if (!statement) {
        return nullptr;
    }
    if (auto conditional = statement->as<If>()) {
        return conditional;
    }
    if (auto block = statement->as<Block>()) {
        if (block->statements().size() == 1 && block->statements().front()->is<If>()) {
            if (!block->declarations().empty()) {
                invalidWrapper = true;
                return nullptr;
            }
            return block->statements().front()->as<If>();
        }
    }
    return nullptr;
}

bool hasSwitchControlStatement(const TreeNode *node,
                               bool breakHasNestedTarget = false) {
    if (!node) {
        return false;
    }
    bool childBreakHasNestedTarget = breakHasNestedTarget;
    if (auto statement = node->as<Statement>()) {
        /*
         * A nested switch owns every break/case/default below it. A loop only
         * owns breaks: case/default labels inside a loop still belong to the
         * nearest surrounding switch, so keep looking for those. Continue is
         * never captured by a newly inserted switch.
         */
        if (statement->statementKind() == Statement::SWITCH) {
            return false;
        }
        if (statement->statementKind() == Statement::BREAK) {
            return !breakHasNestedTarget;
        }
        if (statement->statementKind() == Statement::CASE_LABEL ||
            statement->statementKind() == Statement::DEFAULT_LABEL) {
            return true;
        }
        if (statement->statementKind() == Statement::DO_WHILE ||
            statement->statementKind() == Statement::FOR ||
            statement->statementKind() == Statement::WHILE) {
            childBreakHasNestedTarget = true;
        }
    }

    bool result = false;
    node->callOnChildren([&](const TreeNode *child) {
        if (!result && hasSwitchControlStatement(
                           child, childBreakHasNestedTarget)) {
            result = true;
        }
    });
    return result;
}

void appendSwitchStatement(Block *body, std::unique_ptr<Statement> statement) {
    if (!statement) {
        return;
    }

    if (auto block = statement->as<Block>()) {
        if (block->declarations().empty()) {
            foreach (auto &nestedStatement, block->statements()) {
                body->addStatement(std::move(nestedStatement));
            }
            return;
        }
    }
    body->addStatement(std::move(statement));
}

std::unique_ptr<Expression> takeComparisonOperand(If *conditional, bool takeVariable,
                                                   bool variableIsLeftOperand) {
    auto binary = conditional->condition()->as<BinaryOperator>();
    assert(binary);

    if (takeVariable == variableIsLeftOperand) {
        return std::move(binary->left());
    }
    return std::move(binary->right());
}

std::unique_ptr<Switch> makeSwitchFromIfLadder(std::unique_ptr<If> &root) {
    std::vector<SwitchCase> cases;
    std::unique_ptr<Statement> *defaultStatement = nullptr;
    const VariableDeclaration *switchVariable = nullptr;
    If *conditional = root.get();

    while (conditional) {
        SwitchComparison comparison;
        if (!getSwitchComparison(conditional, comparison)) {
            break;
        }
        if (!switchVariable) {
            switchVariable = comparison.variable;
            /* C and C++ require an integral (or enum) switch expression. */
            if (!switchVariable->type()->isInteger()) {
                return nullptr;
            }
        } else if (switchVariable != comparison.variable) {
            break;
        }

        /*
         * A comparison against a differently sized integer can apply usual
         * arithmetic conversions that are not equivalent to converting the
         * case label to the switch expression's promoted type.
         */
        if (comparison.constant->value().size() != switchVariable->type()->size()) {
            break;
        }

        foreach (const SwitchCase &existing, cases) {
            if (existing.value.value() == comparison.constant->value().value() ||
                existing.value.signedValue() == comparison.constant->value().signedValue()) {
                return nullptr;
            }
        }

        std::unique_ptr<Statement> *matchingStatement = comparison.isEquality
            ? &conditional->thenStatement()
            : &conditional->elseStatement();
        std::unique_ptr<Statement> *nonmatchingStatement = comparison.isEquality
            ? &conditional->elseStatement()
            : &conditional->thenStatement();

        cases.push_back({conditional, comparison.variableIsLeftOperand,
                         matchingStatement, comparison.constant->value()});
        defaultStatement = nonmatchingStatement;

        bool invalidWrapper = false;
        If *next = getNestedIf(nonmatchingStatement->get(), invalidWrapper);
        if (invalidWrapper) {
            return nullptr;
        }
        conditional = next;
    }

    if (cases.size() < 3 || hasSwitchControlStatement(root.get())) {
        return nullptr;
    }

    auto expression = takeComparisonOperand(cases.front().conditional, true,
                                             cases.front().variableIsLeftOperand);
    auto body = std::make_unique<Block>();

    foreach (SwitchCase &item, cases) {
        body->addStatement(std::make_unique<CaseLabel>(
            takeComparisonOperand(item.conditional, false, item.variableIsLeftOperand)));
        appendSwitchStatement(body.get(), std::move(*item.statement));
        body->addStatement(std::make_unique<Break>());
    }

    if (defaultStatement && *defaultStatement) {
        body->addStatement(std::make_unique<DefaultLabel>());
        appendSwitchStatement(body.get(), std::move(*defaultStatement));
    }

    auto result = std::make_unique<Switch>(std::move(expression), std::move(body));
    if (root->statement()) {
        result->setStatement(root->statement());
    }
    return result;
}

std::size_t countVariableReferences(const TreeNode *node,
                                    const VariableDeclaration *declaration) {
    if (!node) {
        return 0;
    }

    if (auto expression = node->as<Expression>()) {
        if (auto identifier = expression->as<VariableIdentifier>()) {
            return identifier->declaration() == declaration ? 1 : 0;
        }
    }

    std::size_t result = 0;
    node->callOnChildren([&](const TreeNode *child) {
        result += countVariableReferences(child, declaration);
    });
    return result;
}

bool ownsDeclaration(const Block *block, const VariableDeclaration *declaration) {
    foreach (const Declaration *item, block->declarations()) {
        if (item == declaration) {
            return true;
        }
    }
    return false;
}

std::size_t countBlockVariableReferences(const Block *block,
                                         const VariableDeclaration *declaration) {
    std::size_t result = 0;
    foreach (const Statement *statement, block->statements()) {
        result += countVariableReferences(statement, declaration);
    }
    foreach (const Declaration *item, block->declarations()) {
        if (auto variable = item->as<VariableDeclaration>()) {
            result += countVariableReferences(variable->initialValue(), declaration);
        }
    }
    return result;
}

/* Treat potentially volatile or faulting memory reads as observable too. */
bool hasSideEffects(const Expression *expression) {
    if (!expression) {
        return false;
    }

    if (expression->is<CallOperator>()) {
        return true;
    }
    if (expression->is<MemberAccessOperator>()) {
        return true;
    }
    if (auto binary = expression->as<BinaryOperator>()) {
        if (binary->operatorKind() == BinaryOperator::ASSIGN ||
            binary->operatorKind() == BinaryOperator::DIV ||
            binary->operatorKind() == BinaryOperator::REM ||
            binary->operatorKind() == BinaryOperator::ARRAY_SUBSCRIPT) {
            return true;
        }
    }
    if (auto unary = expression->as<UnaryOperator>()) {
        if (unary->operatorKind() == UnaryOperator::DEREFERENCE ||
            unary->operatorKind() == UnaryOperator::PREFIX_INCREMENT ||
            unary->operatorKind() == UnaryOperator::PREFIX_DECREMENT) {
            return true;
        }
    }

    bool result = false;
    expression->callOnChildren([&](const TreeNode *child) {
        if (!result) {
            if (auto childExpression = child->as<Expression>()) {
                result = hasSideEffects(childExpression);
            }
        }
    });
    return result;
}

/*
 * Returns whether an expression can be evaluated on either side of a moved
 * call without changing observable state.  Reads of unrelated variables are
 * intentionally rejected: the moved call could modify the storage they read.
 */
bool isStableAroundVariable(const Expression *expression,
                            const VariableDeclaration *declaration) {
    switch (expression->expressionKind()) {
        case Expression::VARIABLE_IDENTIFIER:
            return expression->as<VariableIdentifier>()->declaration() == declaration;
        case Expression::FUNCTION_IDENTIFIER:
        case Expression::INTEGER_CONSTANT:
        case Expression::LABEL_IDENTIFIER:
        case Expression::STRING:
            return true;
        case Expression::BINARY_OPERATOR: {
            auto binary = expression->as<BinaryOperator>();
            return binary->operatorKind() != BinaryOperator::ASSIGN &&
                   binary->operatorKind() != BinaryOperator::LOGICAL_AND &&
                   binary->operatorKind() != BinaryOperator::LOGICAL_OR &&
                   isStableAroundVariable(binary->left(), declaration) &&
                   isStableAroundVariable(binary->right(), declaration);
        }
        case Expression::TYPECAST:
            return isStableAroundVariable(expression->as<Typecast>()->operand(), declaration);
        case Expression::UNARY_OPERATOR: {
            auto unary = expression->as<UnaryOperator>();
            switch (unary->operatorKind()) {
                case UnaryOperator::BITWISE_NOT:
                case UnaryOperator::LOGICAL_NOT:
                case UnaryOperator::NEGATION:
                    return isStableAroundVariable(unary->operand(), declaration);
                default:
                    return false;
            }
        }
        case Expression::CALL_OPERATOR:
        case Expression::MEMBER_ACCESS_OPERATOR:
        case Expression::UNDECLARED_IDENTIFIER:
            return false;
    }
    unreachable();
}

std::unique_ptr<Expression> *statementExpression(Statement *statement,
                                                 bool allowConditional) {
    if (auto expressionStatement = statement->as<ExpressionStatement>()) {
        return &expressionStatement->expression();
    }
    if (allowConditional) {
        if (auto conditional = statement->as<If>()) {
            return &conditional->condition();
        }
    }
    if (auto returnStatement = statement->as<Return>()) {
        if (returnStatement->returnValue()) {
            return &returnStatement->returnValue();
        }
    }
    return nullptr;
}

bool isSafeInliningDestination(const Expression *expression,
                               const VariableDeclaration *declaration,
                               bool sourceHasSideEffects) {
    const Expression *payload = expression;

    if (auto assignment = payload->as<BinaryOperator>()) {
        if (assignment->operatorKind() == BinaryOperator::ASSIGN) {
            if (countVariableReferences(assignment->left(), declaration) != 0 ||
                hasSideEffects(assignment->left()) ||
                (sourceHasSideEffects &&
                 !assignment->left()->is<VariableIdentifier>() &&
                 !assignment->left()->is<UndeclaredIdentifier>())) {
                return false;
            }
            payload = assignment->right();
        }
    }

    if (auto call = payload->as<CallOperator>()) {
        if (countVariableReferences(call->callee(), declaration) != 0 ||
            hasSideEffects(call->callee()) ||
            (sourceHasSideEffects &&
             !isStableAroundVariable(call->callee(), declaration))) {
            return false;
        }
        foreach (const Expression *argument, call->arguments()) {
            if (hasSideEffects(argument)) {
                return false;
            }
            if (sourceHasSideEffects &&
                !isStableAroundVariable(argument, declaration)) {
                return false;
            }
        }
    } else {
        if (hasSideEffects(payload)) {
            return false;
        }
        if (sourceHasSideEffects &&
            !isStableAroundVariable(payload, declaration)) {
            return false;
        }
    }

    return countVariableReferences(payload, declaration) == 1;
}

enum VariableUseContext {
    READ_VARIABLE,
    FORBID_VARIABLE
};

struct ReplacementSite {
    std::unique_ptr<Expression> *expression = nullptr;
    std::size_t uses = 0;
    bool invalid = false;
};

void findReplacementSite(std::unique_ptr<Expression> &expression,
                         const VariableDeclaration *declaration,
                         VariableUseContext context,
                         ReplacementSite &result) {
    if (auto identifier = expression->as<VariableIdentifier>()) {
        if (identifier->declaration() == declaration) {
            ++result.uses;
            if (context == FORBID_VARIABLE || result.expression) {
                result.invalid = true;
            } else {
                result.expression = &expression;
            }
        }
        return;
    }

    switch (expression->expressionKind()) {
        case Expression::BINARY_OPERATOR: {
            auto binary = expression->as<BinaryOperator>();
            if (binary->operatorKind() == BinaryOperator::ASSIGN) {
                findReplacementSite(binary->left(), declaration, FORBID_VARIABLE, result);
                findReplacementSite(binary->right(), declaration, context, result);
            } else {
                findReplacementSite(binary->left(), declaration, context, result);
                findReplacementSite(binary->right(), declaration, context, result);
            }
            break;
        }
        case Expression::CALL_OPERATOR: {
            auto call = expression->as<CallOperator>();
            findReplacementSite(call->callee(), declaration, FORBID_VARIABLE, result);
            foreach (auto &argument, call->arguments()) {
                findReplacementSite(argument, declaration, context, result);
            }
            break;
        }
        case Expression::MEMBER_ACCESS_OPERATOR:
            findReplacementSite(expression->as<MemberAccessOperator>()->compound(),
                                declaration, context, result);
            break;
        case Expression::TYPECAST:
            findReplacementSite(expression->as<Typecast>()->operand(),
                                declaration, context, result);
            break;
        case Expression::UNARY_OPERATOR: {
            auto unary = expression->as<UnaryOperator>();
            VariableUseContext operandContext = context;
            if (unary->operatorKind() == UnaryOperator::REFERENCE ||
                unary->operatorKind() == UnaryOperator::PREFIX_INCREMENT ||
                unary->operatorKind() == UnaryOperator::PREFIX_DECREMENT) {
                operandContext = FORBID_VARIABLE;
            }
            findReplacementSite(unary->operand(), declaration, operandContext, result);
            break;
        }
        case Expression::FUNCTION_IDENTIFIER:
        case Expression::INTEGER_CONSTANT:
        case Expression::LABEL_IDENTIFIER:
        case Expression::STRING:
        case Expression::VARIABLE_IDENTIFIER:
        case Expression::UNDECLARED_IDENTIFIER:
            break;
    }
}

bool inlineSingleUseTemporary(Block *block, const Block *outerDeclarationScope,
                              bool allowConditional,
                              TypeCalculator &typeCalculator) {
    auto &statements = block->statements();

    for (std::size_t i = 0; i + 1 < statements.size(); ++i) {
        auto expressionStatement = statements[i]->as<ExpressionStatement>();
        if (!expressionStatement) {
            continue;
        }
        auto assignment = expressionStatement->expression()->as<BinaryOperator>();
        if (!assignment || assignment->operatorKind() != BinaryOperator::ASSIGN) {
            continue;
        }
        auto identifier = assignment->left()->as<VariableIdentifier>();
        if (!identifier) {
            continue;
        }

        VariableDeclaration *declaration = identifier->declaration();
        const Block *referenceScope = nullptr;
        if (ownsDeclaration(block, declaration)) {
            referenceScope = block;
        } else if (outerDeclarationScope &&
                   ownsDeclaration(outerDeclarationScope, declaration)) {
            referenceScope = outerDeclarationScope;
        }
        if (!referenceScope || declaration->initialValue()) {
            continue;
        }

        /*
         * The assignment may narrow or otherwise convert its right operand.
         * Dropping that conversion while substituting the operand changes the
         * value observed at the use site.  Keep floating-point stores too,
         * since they can round excess precision before the later load.
         */
        const Type *temporaryType = declaration->type();
        if (!temporaryType->isScalar() || temporaryType->isFloat() ||
            typeCalculator.getType(assignment->right().get()) != temporaryType) {
            continue;
        }

        if (countBlockVariableReferences(referenceScope, declaration) != 2 ||
            countVariableReferences(assignment->right().get(), declaration) != 0 ||
            countVariableReferences(statements[i + 1].get(), declaration) != 1) {
            continue;
        }

        auto destination = statementExpression(statements[i + 1].get(),
                                                allowConditional);
        if (!destination ||
            !isSafeInliningDestination(destination->get(), declaration,
                                       hasSideEffects(assignment->right().get()))) {
            continue;
        }

        ReplacementSite replacementSite;
        findReplacementSite(*destination, declaration, READ_VARIABLE, replacementSite);
        if (replacementSite.invalid || replacementSite.uses != 1 ||
            !replacementSite.expression) {
            continue;
        }

        *replacementSite.expression = std::move(assignment->right());
        statements.erase(statements.begin() + i);
        return true;
    }

    return false;
}

bool inlineFunctionScopeTemporary(TreeNode *node, Block *functionBlock,
                                  TypeCalculator &typeCalculator) {
    if (!node) {
        return false;
    }

    if (auto statement = node->as<Statement>()) {
        if (auto block = statement->as<Block>()) {
            if (inlineSingleUseTemporary(block, functionBlock, true,
                                         typeCalculator)) {
                return true;
            }
        }
    }

    bool result = false;
    node->callOnChildren([&](TreeNode *child) {
        if (!result) {
            result = inlineFunctionScopeTemporary(
                child, functionBlock, typeCalculator);
        }
    });
    return result;
}

bool removeDeadLocalAssignment(Block *block) {
    auto &statements = block->statements();

    for (auto i = statements.begin(); i != statements.end(); ++i) {
        auto expressionStatement = (*i)->as<ExpressionStatement>();
        if (!expressionStatement) {
            continue;
        }
        auto assignment = expressionStatement->expression()->as<BinaryOperator>();
        if (!assignment || assignment->operatorKind() != BinaryOperator::ASSIGN) {
            continue;
        }
        auto identifier = assignment->left()->as<VariableIdentifier>();
        if (!identifier) {
            continue;
        }

        VariableDeclaration *declaration = identifier->declaration();
        if (!ownsDeclaration(block, declaration) || declaration->initialValue() ||
            hasSideEffects(assignment->right().get()) ||
            countVariableReferences(assignment->right().get(), declaration) != 0 ||
            countBlockVariableReferences(block, declaration) != 1) {
            continue;
        }

        statements.erase(i);
        return true;
    }

    return false;
}

bool hasLoopTransfer(const TreeNode *node) {
    if (!node) {
        return false;
    }
    if (auto statement = node->as<Statement>()) {
        if (statement->statementKind() == Statement::CONTINUE ||
            statement->statementKind() == Statement::GOTO ||
            statement->statementKind() == Statement::LABEL_STATEMENT) {
            return true;
        }
    }

    bool result = false;
    node->callOnChildren([&](const TreeNode *child) {
        if (!result) {
            result = hasLoopTransfer(child);
        }
    });
    return result;
}

bool hasUnsafeInductionAccess(const TreeNode *node,
                              const VariableDeclaration *declaration) {
    if (!node) {
        return false;
    }

    if (auto expression = node->as<Expression>()) {
        if (auto binary = expression->as<BinaryOperator>()) {
            if (binary->operatorKind() == BinaryOperator::ASSIGN) {
                if (auto identifier = binary->left()->as<VariableIdentifier>()) {
                    if (identifier->declaration() == declaration) {
                        return true;
                    }
                }
            }
        }
        if (auto unary = expression->as<UnaryOperator>()) {
            if ((unary->operatorKind() == UnaryOperator::REFERENCE ||
                 unary->operatorKind() == UnaryOperator::PREFIX_INCREMENT ||
                 unary->operatorKind() == UnaryOperator::PREFIX_DECREMENT) &&
                countVariableReferences(unary->operand(), declaration) != 0) {
                return true;
            }
        }
    }

    bool result = false;
    node->callOnChildren([&](const TreeNode *child) {
        if (!result) {
            result = hasUnsafeInductionAccess(child, declaration);
        }
    });
    return result;
}

VariableDeclaration *assignedVariable(ExpressionStatement *statement) {
    auto assignment = statement->expression()->as<BinaryOperator>();
    if (!assignment || assignment->operatorKind() != BinaryOperator::ASSIGN) {
        return nullptr;
    }
    auto identifier = assignment->left()->as<VariableIdentifier>();
    return identifier ? identifier->declaration() : nullptr;
}

bool isIncrementOf(const Expression *expression,
                   const VariableDeclaration *declaration) {
    auto unary = expression->as<UnaryOperator>();
    if (!unary ||
        (unary->operatorKind() != UnaryOperator::PREFIX_INCREMENT &&
         unary->operatorKind() != UnaryOperator::PREFIX_DECREMENT)) {
        return false;
    }
    auto identifier = unary->operand()->as<VariableIdentifier>();
    return identifier && identifier->declaration() == declaration;
}

bool isPositiveIncrementOf(const Expression *expression,
                           const VariableDeclaration *declaration) {
    auto unary = expression->as<UnaryOperator>();
    if (!unary || unary->operatorKind() != UnaryOperator::PREFIX_INCREMENT) {
        return false;
    }
    auto identifier = unary->operand()->as<VariableIdentifier>();
    return identifier && identifier->declaration() == declaration;
}

const VariableIdentifier *variableIdentifierThroughCasts(const Expression *expression) {
    while (auto typecast = expression->as<Typecast>()) {
        expression = typecast->operand();
    }
    return expression->as<VariableIdentifier>();
}

bool isZeroAssignment(ExpressionStatement *statement,
                      VariableDeclaration *&declaration) {
    auto assignment = statement->expression()->as<BinaryOperator>();
    if (!assignment || assignment->operatorKind() != BinaryOperator::ASSIGN ||
        !isZero(assignment->right().get())) {
        return false;
    }

    auto identifier = assignment->left()->as<VariableIdentifier>();
    if (!identifier) {
        return false;
    }
    declaration = identifier->declaration();
    return true;
}

bool sameStableExpression(const Expression *left, const Expression *right) {
    if (left->expressionKind() != right->expressionKind()) {
        return false;
    }

    switch (left->expressionKind()) {
        case Expression::VARIABLE_IDENTIFIER:
            return left->as<VariableIdentifier>()->declaration() ==
                   right->as<VariableIdentifier>()->declaration();
        case Expression::INTEGER_CONSTANT: {
            auto leftConstant = left->as<IntegerConstant>();
            auto rightConstant = right->as<IntegerConstant>();
            return leftConstant->type() == rightConstant->type() &&
                   leftConstant->value().value() == rightConstant->value().value();
        }
        case Expression::TYPECAST: {
            auto leftCast = left->as<Typecast>();
            auto rightCast = right->as<Typecast>();
            return leftCast->castKind() == rightCast->castKind() &&
                   leftCast->type() == rightCast->type() &&
                   sameStableExpression(leftCast->operand(), rightCast->operand());
        }
        case Expression::UNARY_OPERATOR: {
            auto leftUnary = left->as<UnaryOperator>();
            auto rightUnary = right->as<UnaryOperator>();
            return leftUnary->operatorKind() == UnaryOperator::REFERENCE &&
                   rightUnary->operatorKind() == UnaryOperator::REFERENCE &&
                   sameStableExpression(leftUnary->operand(), rightUnary->operand());
        }
        case Expression::BINARY_OPERATOR: {
            auto leftBinary = left->as<BinaryOperator>();
            auto rightBinary = right->as<BinaryOperator>();
            const int operatorKind = leftBinary->operatorKind();
            if (operatorKind != rightBinary->operatorKind() ||
                (operatorKind != BinaryOperator::ADD &&
                 operatorKind != BinaryOperator::SUB &&
                 operatorKind != BinaryOperator::ARRAY_SUBSCRIPT)) {
                return false;
            }
            return sameStableExpression(leftBinary->left(), rightBinary->left()) &&
                   sameStableExpression(leftBinary->right(), rightBinary->right());
        }
        case Expression::CALL_OPERATOR:
        case Expression::FUNCTION_IDENTIFIER:
        case Expression::LABEL_IDENTIFIER:
        case Expression::MEMBER_ACCESS_OPERATOR:
        case Expression::STRING:
        case Expression::UNDECLARED_IDENTIFIER:
            return false;
    }
    unreachable();
}

bool sameStrlenCall(const Expression *left, const Expression *right) {
    while (auto leftCast = left->as<Typecast>()) {
        auto rightCast = right->as<Typecast>();
        if (!rightCast || leftCast->castKind() != rightCast->castKind() ||
            leftCast->type() != rightCast->type()) {
            return false;
        }
        left = leftCast->operand();
        right = rightCast->operand();
    }
    if (right->is<Typecast>()) {
        return false;
    }

    auto leftCall = left->as<CallOperator>();
    auto rightCall = right->as<CallOperator>();
    if (!leftCall || !rightCall || leftCall->arguments().size() != 1 ||
        rightCall->arguments().size() != 1) {
        return false;
    }

    auto leftCallee = leftCall->callee()->as<UndeclaredIdentifier>();
    auto rightCallee = rightCall->callee()->as<UndeclaredIdentifier>();
    return leftCallee && rightCallee &&
           leftCallee->name() == QLatin1String("strlen") &&
           rightCallee->name() == QLatin1String("strlen") &&
           sameStableExpression(leftCall->arguments().front(),
                                rightCall->arguments().front());
}

const Expression *expressionThroughCasts(const Expression *expression) {
    while (auto typecast = expression->as<Typecast>()) {
        expression = typecast->operand();
    }
    return expression;
}

const VariableDeclaration *variableAtDeclaredType(const Expression *expression) {
    const Type *castType = nullptr;
    while (auto typecast = expression->as<Typecast>()) {
        if (castType && castType != typecast->type()) {
            return nullptr;
        }
        castType = typecast->type();
        expression = typecast->operand();
    }
    auto identifier = expression->as<VariableIdentifier>();
    if (!identifier) {
        return nullptr;
    }
    const VariableDeclaration *declaration = identifier->declaration();
    return !castType || castType == declaration->type() ? declaration : nullptr;
}

const VariableDeclaration *zeroEqualityVariable(const Expression *expression) {
    expression = expressionThroughCasts(expression);
    if (auto logicalNot = expression->as<UnaryOperator>()) {
        if (logicalNot->operatorKind() == UnaryOperator::LOGICAL_NOT) {
            return variableAtDeclaredType(logicalNot->operand());
        }
    }

    auto comparison = expression->as<BinaryOperator>();
    if (!comparison || comparison->operatorKind() != BinaryOperator::EQ) {
        return nullptr;
    }
    const Expression *variable = nullptr;
    if (isZero(comparison->right())) {
        variable = comparison->left();
    } else if (isZero(comparison->left())) {
        variable = comparison->right();
    }
    return variable ? variableAtDeclaredType(variable) : nullptr;
}

const VariableDeclaration *negativeComparisonVariable(const Expression *expression) {
    expression = expressionThroughCasts(expression);
    auto comparison = expression->as<BinaryOperator>();
    if (!comparison) {
        return nullptr;
    }

    const Expression *variable = nullptr;
    if (comparison->operatorKind() == BinaryOperator::LT &&
        isZero(comparison->right())) {
        variable = comparison->left();
    } else if (comparison->operatorKind() == BinaryOperator::GT &&
               isZero(comparison->left())) {
        variable = comparison->right();
    } else {
        return nullptr;
    }

    const VariableDeclaration *declaration = variableAtDeclaredType(variable);
    if (!declaration) {
        return nullptr;
    }
    auto integerType = declaration->type()->as<IntegerType>();
    return integerType && integerType->isSigned() ? declaration : nullptr;
}

const VariableDeclaration *positiveComparisonVariable(const Expression *expression) {
    expression = expressionThroughCasts(expression);
    if (auto comparison = expression->as<BinaryOperator>()) {
        const Expression *variable = nullptr;
        const Expression *zero = nullptr;
        if (comparison->operatorKind() == BinaryOperator::GT) {
            variable = comparison->left();
            zero = comparison->right();
        } else if (comparison->operatorKind() == BinaryOperator::LT) {
            zero = comparison->left();
            variable = comparison->right();
        }
        return variable && isZero(zero) ? variableAtDeclaredType(variable) : nullptr;
    }

    auto logicalNot = expression->as<UnaryOperator>();
    if (!logicalNot || logicalNot->operatorKind() != UnaryOperator::LOGICAL_NOT) {
        return nullptr;
    }
    auto disjunction = expressionThroughCasts(logicalNot->operand())
        ->as<BinaryOperator>();
    if (!disjunction ||
        (disjunction->operatorKind() != BinaryOperator::LOGICAL_OR &&
         disjunction->operatorKind() != BinaryOperator::BITWISE_OR)) {
        return nullptr;
    }

    const VariableDeclaration *negative =
        negativeComparisonVariable(disjunction->left());
    const VariableDeclaration *zero =
        zeroEqualityVariable(disjunction->right());
    if (!negative || negative != zero) {
        negative = negativeComparisonVariable(disjunction->right());
        zero = zeroEqualityVariable(disjunction->left());
    }
    return negative && negative == zero ? negative : nullptr;
}

bool isCanonicalIndexReset(const Statement *statement,
                           const VariableDeclaration *index) {
    auto conditional = statement->as<If>();
    if (!conditional || conditional->elseStatement()) {
        return false;
    }

    auto comparison = conditional->condition()->as<BinaryOperator>();
    if (!comparison) {
        return false;
    }
    const Expression *variable = nullptr;
    const IntegerConstant *limit = nullptr;
    if (comparison->operatorKind() == BinaryOperator::GEQ) {
        variable = comparison->left();
        limit = comparison->right()->as<IntegerConstant>();
    } else if (comparison->operatorKind() == BinaryOperator::LEQ) {
        variable = comparison->right();
        limit = comparison->left()->as<IntegerConstant>();
    }
    auto identifier = variable ? variableIdentifierThroughCasts(variable) : nullptr;
    if (!identifier || identifier->declaration() != index || !limit ||
        limit->value().value() == 0) {
        return false;
    }

    const Statement *resetStatement = conditional->thenStatement();
    if (auto block = resetStatement->as<Block>()) {
        if (!block->declarations().empty() || block->statements().size() != 1) {
            return false;
        }
        resetStatement = block->statements().front();
    }
    auto expressionStatement = resetStatement->as<ExpressionStatement>();
    if (!expressionStatement) {
        return false;
    }
    auto assignment = expressionStatement->expression()->as<BinaryOperator>();
    if (!assignment || assignment->operatorKind() != BinaryOperator::ASSIGN ||
        !isZero(assignment->right())) {
        return false;
    }
    auto resetIdentifier = assignment->left()->as<VariableIdentifier>();
    return resetIdentifier && resetIdentifier->declaration() == index;
}

void recoverGuardedDoWhileForLoops(Block *block, TypeCalculator &typeCalculator) {
    auto &statements = block->statements();

    for (std::size_t i = 3; i < statements.size(); ++i) {
        auto counterInitializer = statements[i - 3]->as<ExpressionStatement>();
        auto indexInitializer = statements[i - 2]->as<ExpressionStatement>();
        auto lengthInitializer = statements[i - 1]->as<ExpressionStatement>();
        auto conditional = statements[i]->as<If>();
        if (!counterInitializer || !indexInitializer || !lengthInitializer ||
            !conditional || conditional->elseStatement()) {
            continue;
        }

        VariableDeclaration *counter = nullptr;
        VariableDeclaration *index = nullptr;
        if (!isZeroAssignment(counterInitializer, counter) ||
            !isZeroAssignment(indexInitializer, index) || counter == index ||
            !ownsDeclaration(block, counter) || !ownsDeclaration(block, index) ||
            counter->initialValue() || index->initialValue()) {
            continue;
        }

        auto initialLengthAssignment =
            lengthInitializer->expression()->as<BinaryOperator>();
        VariableDeclaration *initialLength = assignedVariable(lengthInitializer);
        if (!initialLengthAssignment || !initialLength ||
            positiveComparisonVariable(conditional->condition().get()) != initialLength ||
            !ownsDeclaration(block, initialLength) || initialLength->initialValue()) {
            continue;
        }

        DoWhile *loop = conditional->thenStatement()->as<DoWhile>();
        Block *wrapper = conditional->thenStatement()->as<Block>();
        if (!loop && wrapper && wrapper->declarations().empty() &&
            wrapper->statements().size() == 1) {
            loop = wrapper->statements().front()->as<DoWhile>();
        }
        auto body = loop ? loop->body()->as<Block>() : nullptr;
        if (!loop || !body || body->statements().size() < 2 ||
            hasLoopTransfer(body)) {
            continue;
        }

        auto incrementStatement =
            body->statements()[body->statements().size() - 2]->as<ExpressionStatement>();
        auto tailLengthStatement = body->statements().back()->as<ExpressionStatement>();
        if (!incrementStatement || !tailLengthStatement ||
            !isPositiveIncrementOf(incrementStatement->expression().get(), index)) {
            continue;
        }

        auto tailLengthAssignment =
            tailLengthStatement->expression()->as<BinaryOperator>();
        VariableDeclaration *tailLength = assignedVariable(tailLengthStatement);
        if (!tailLengthAssignment || !tailLength ||
            !ownsDeclaration(block, tailLength) || tailLength->initialValue() ||
            initialLength == counter || initialLength == index ||
            tailLength == counter || tailLength == index ||
            initialLength->type() != tailLength->type() ||
            typeCalculator.getType(initialLengthAssignment->right().get()) !=
                initialLength->type() ||
            typeCalculator.getType(tailLengthAssignment->right().get()) !=
                tailLength->type() ||
            !sameStrlenCall(initialLengthAssignment->right().get(),
                            tailLengthAssignment->right().get())) {
            continue;
        }

        auto tailCondition = loop->condition()->as<BinaryOperator>();
        if (!tailCondition || tailCondition->operatorKind() != BinaryOperator::LT) {
            continue;
        }
        auto tailCounter = variableIdentifierThroughCasts(tailCondition->left().get());
        auto tailLengthIdentifier = tailCondition->right()->as<VariableIdentifier>();
        if (!tailCounter || tailCounter->declaration() != counter ||
            !tailLengthIdentifier || tailLengthIdentifier->declaration() != tailLength) {
            continue;
        }

        std::size_t expectedInitialLengthReferences = 1 +
            countVariableReferences(conditional->condition().get(), initialLength);
        if (initialLength == tailLength) {
            expectedInitialLengthReferences += 2;
        }
        if (countBlockVariableReferences(block, initialLength) !=
                expectedInitialLengthReferences ||
            (initialLength != tailLength &&
             countBlockVariableReferences(block, tailLength) != 2)) {
            continue;
        }

        bool sawIndexReset = false;
        bool unsafeIndexWrite = false;
        std::size_t counterIncrements = 0;
        bool unsafeCounterWrite = false;
        for (std::size_t j = 0; j + 2 < body->statements().size(); ++j) {
            Statement *statement = body->statements()[j].get();
            if (!sawIndexReset && isCanonicalIndexReset(statement, index)) {
                sawIndexReset = true;
            } else if (hasUnsafeInductionAccess(statement, index)) {
                unsafeIndexWrite = true;
                break;
            }

            if (auto expressionStatement = statement->as<ExpressionStatement>()) {
                if (isPositiveIncrementOf(expressionStatement->expression().get(),
                                          counter)) {
                    ++counterIncrements;
                    continue;
                }
            }
            if (hasUnsafeInductionAccess(statement, counter)) {
                unsafeCounterWrite = true;
                break;
            }
        }
        if (unsafeIndexWrite || unsafeCounterWrite || counterIncrements != 1) {
            continue;
        }

        auto initializerExpression = indexInitializer->releaseExpression();
        auto incrementExpression = incrementStatement->releaseExpression();
        auto conditionExpression = std::make_unique<BinaryOperator>(
            BinaryOperator::LT, std::move(tailCondition->left()),
            std::move(tailLengthAssignment->right()));
        body->statements().erase(body->statements().end() - 2,
                                 body->statements().end());

        std::unique_ptr<Statement> loopStatement;
        if (wrapper) {
            loopStatement = std::move(wrapper->statements().front());
        } else {
            loopStatement = std::move(conditional->thenStatement());
        }
        auto doWhileNode = as<DoWhile>(std::move(loopStatement));
        const ir::Statement *irStatement = doWhileNode->statement();
        if (!irStatement) {
            irStatement = conditional->statement();
        }
        auto forNode = std::make_unique<For>(
            std::move(initializerExpression), std::move(conditionExpression),
            std::move(incrementExpression), std::move(doWhileNode->body()));
        if (irStatement) {
            forNode->setStatement(irStatement);
        }

        statements[i] = std::move(forNode);
        statements.erase(statements.begin() + i - 2, statements.begin() + i);
        i -= 2;
    }
}

void recoverForLoops(Block *block) {
    auto &statements = block->statements();

    for (std::size_t i = 1; i < statements.size(); ++i) {
        auto initializerStatement = statements[i - 1]->as<ExpressionStatement>();
        auto loop = statements[i]->as<While>();
        if (!initializerStatement || !loop) {
            continue;
        }

        VariableDeclaration *declaration = assignedVariable(initializerStatement);
        auto initializer = initializerStatement->expression()->as<BinaryOperator>();
        auto body = loop->body()->as<Block>();
        if (!declaration || !initializer || !ownsDeclaration(block, declaration) ||
            declaration->initialValue() || !body || body->statements().empty() ||
            countVariableReferences(initializer->right().get(), declaration) != 0 ||
            hasUnsafeInductionAccess(loop->condition().get(), declaration) ||
            hasLoopTransfer(body)) {
            continue;
        }

        auto incrementStatement = body->statements().back()->as<ExpressionStatement>();
        if (!incrementStatement ||
            !isIncrementOf(incrementStatement->expression().get(), declaration)) {
            continue;
        }

        bool unsafeBody = false;
        for (std::size_t j = 0; j + 1 < body->statements().size(); ++j) {
            if (hasUnsafeInductionAccess(body->statements()[j].get(), declaration)) {
                unsafeBody = true;
                break;
            }
        }
        if (unsafeBody) {
            continue;
        }

        auto initializerExpression = initializerStatement->releaseExpression();
        auto incrementExpression = incrementStatement->releaseExpression();
        body->statements().pop_back();

        auto whileNode = as<While>(std::move(statements[i]));
        const ir::Statement *irStatement = whileNode->statement();
        auto forNode = std::make_unique<For>(
            std::move(initializerExpression), std::move(whileNode->condition()),
            std::move(incrementExpression), std::move(whileNode->body()));
        if (irStatement) {
            forNode->setStatement(irStatement);
        }
        statements[i] = std::move(forNode);
        statements.erase(statements.begin() + i - 1);

        if (i > 1) {
            --i;
        }
    }
}

void pruneUnusedDeclarations(Block *block) {
    auto &declarations = block->declarations();
    std::vector<const Declaration *> unused;
    const Block *constBlock = block;

    foreach (const Declaration *item, constBlock->declarations()) {
        auto variable = item->as<VariableDeclaration>();
        if (!variable || variable->initialValue()) {
            continue;
        }

        bool referenced = false;
        foreach (const Statement *statement, constBlock->statements()) {
            if (countVariableReferences(statement, variable) != 0) {
                referenced = true;
                break;
            }
        }
        if (referenced) {
            continue;
        }

        foreach (const Declaration *other, constBlock->declarations()) {
            if (other == variable) {
                continue;
            }
            if (auto otherVariable = other->as<VariableDeclaration>()) {
                if (countVariableReferences(otherVariable->initialValue(), variable) != 0) {
                    referenced = true;
                    break;
                }
            }
        }
        if (!referenced) {
            unused.push_back(item);
        }
    }

    declarations.erase(std::remove_if(declarations.begin(), declarations.end(),
        [&](const std::unique_ptr<Declaration> &item) {
            return std::find(unused.begin(), unused.end(), item.get()) != unused.end();
        }), declarations.end());
}

} // anonymous namespace

Simplifier::Simplifier(Tree &tree) : typeCalculator_(tree) {
}

std::unique_ptr<CompilationUnit> Simplifier::simplify(std::unique_ptr<CompilationUnit> node) {
    node->declarations() = simplify(std::move(node->declarations()));
    return node;
}

std::unique_ptr<Declaration> Simplifier::simplify(std::unique_ptr<Declaration> node) {
    switch (node->declarationKind()) {
        case Declaration::FUNCTION_DECLARATION:
            return node;
        case Declaration::FUNCTION_DEFINITION:
            return simplify(as<FunctionDefinition>(std::move(node)));
        case Declaration::LABEL_DECLARATION:
            return simplify(as<LabelDeclaration>(std::move(node)));
        case Declaration::MEMBER_DECLARATION:
            return node;
        case Declaration::STRUCT_TYPE_DECLARATION:
            return node;
        case Declaration::VARIABLE_DECLARATION:
            return simplify(as<VariableDeclaration>(std::move(node)));
    }
    unreachable();
}

std::unique_ptr<FunctionDefinition> Simplifier::simplify(std::unique_ptr<FunctionDefinition> node) {
    node->block() = simplify(std::move(node->block()));

    /*
     * DefinitionGenerator declares all recovered locals in the function's
     * outer block, even when an assignment and its sole use live together in
     * a nested branch.  Run this only after the complete function block is
     * back in place, so the reference count covers every branch.  Each
     * successful iteration removes an assignment, making the fixed point
     * finite; re-simplifying also prunes its now-unused declaration and can
     * expose structured control flow.
     */
    bool changed;
    do {
        changed = false;
        while (inlineFunctionScopeTemporary(
                   node->block().get(), node->block().get(), typeCalculator_)) {
            changed = true;
        }
        if (changed) {
            node->block() = simplify(std::move(node->block()));
        }
    } while (changed);

    node->labels() = simplify(std::move(node->labels()));
    return node;
}

std::unique_ptr<LabelDeclaration> Simplifier::simplify(std::unique_ptr<LabelDeclaration> node) {
    return node;
}

std::unique_ptr<VariableDeclaration> Simplifier::simplify(std::unique_ptr<VariableDeclaration> node) {
    if (node->initialValue()) {
        node->initialValue() = std::move(node->initialValue());
    }
    return node;
}

std::unique_ptr<Expression> Simplifier::simplify(std::unique_ptr<Expression> node) {
    switch (node->expressionKind()) {
        case Expression::BINARY_OPERATOR:
            return simplify(as<BinaryOperator>(std::move(node)));
        case Expression::CALL_OPERATOR:
            return simplify(as<CallOperator>(std::move(node)));
        case Expression::FUNCTION_IDENTIFIER:
            return node;
        case Expression::INTEGER_CONSTANT:
            return node;
        case Expression::LABEL_IDENTIFIER:
            return node;
        case Expression::MEMBER_ACCESS_OPERATOR:
            return simplify(as<MemberAccessOperator>(std::move(node)));
        case Expression::STRING:
            return node;
        case Expression::TYPECAST:
            return simplify(as<Typecast>(std::move(node)));
        case Expression::UNARY_OPERATOR:
            return simplify(as<UnaryOperator>(std::move(node)));
        case Expression::VARIABLE_IDENTIFIER:
            return node;
        case Expression::UNDECLARED_IDENTIFIER:
            return node;
    }
    unreachable();
}

std::unique_ptr<Expression> Simplifier::simplify(std::unique_ptr<BinaryOperator> node) {
    node->left() = simplify(std::move(node->left()));
    node->right() = simplify(std::move(node->right()));

    /* Remove typecasts of operands if this won't change anything. */
    switch (node->operatorKind()) {
        case BinaryOperator::ADD:
        case BinaryOperator::SUB:
        case BinaryOperator::MUL:
        case BinaryOperator::DIV:
        case BinaryOperator::REM: {
            auto rewrite = [&](std::unique_ptr<Expression> &left, std::unique_ptr<Expression> &right) {
                if (auto typecast = left->as<Typecast>()) {
                    if (typecast->type()->size() >= typeCalculator_.getType(typecast->operand().get())->size()) {
                        if (typeCalculator_.getType(node.get()) ==
                            typeCalculator_.getBinaryOperatorType(node->operatorKind(), typecast->operand().get(),
                                                                  right.get())) {
                            left = std::move(typecast->operand());
                        }
                    }
                }
            };
            rewrite(node->left(), node->right());
            rewrite(node->right(), node->left());
            break;
        }
        default:
            break;
    }

    /* Rewrite computing of member address. */
    if (node->operatorKind() == BinaryOperator::ADD) {
        auto rewrite = [&](Expression *left, Expression *right) -> std::unique_ptr<Expression> {
            if (auto typecast = left->as<Typecast>()) {
                if (typecast->type()->isInteger() &&
                    typecast->type()->size() == typeCalculator_.getType(typecast->operand().get())->size()) {
                    if (auto pointerType = typeCalculator_.getType(typecast->operand().get())->as<PointerType>()) {
                        if (auto structType = pointerType->pointeeType()->as<StructType>()) {
                            if (auto constant = right->as<IntegerConstant>()) {
                                if (const MemberDeclaration *member =
                                        structType->getMember(constant->value().value() * CHAR_BIT)) {
                                    return simplify(std::make_unique<UnaryOperator>(
                                        UnaryOperator::REFERENCE,
                                        std::make_unique<MemberAccessOperator>(
                                            MemberAccessOperator::ARROW, std::move(typecast->operand()), member)));
                                }
                            }
                        }
                    }
                }
            }
            return nullptr;
        };
        if (auto result = rewrite(node->left().get(), node->right().get())) {
            return result;
        }
        if (auto result = rewrite(node->right().get(), node->left().get())) {
            return result;
        }
    }

    /*
     * Handling pointer arithmetic:
     *
     * rdi2 = (int32_t*)((int64_t)rdi2 + 4); -> rdi2 = (int32_t*)(int64_t)(rdi2 + 1);
     */

    auto rewritePointerArithmetic = [&](Expression *left, Expression *right) -> std::unique_ptr<BinaryOperator> {
        if (auto typecast = left->as<Typecast>()) {
            if (typecast->type()->isInteger() &&
                typecast->type()->size() == typeCalculator_.getType(typecast->operand().get())->size()) {
                if (auto pointerType = typeCalculator_.getType(typecast->operand().get())->as<PointerType>()) {
                    if (pointerType->pointeeType()->size() != 0 && pointerType->pointeeType()->size() % CHAR_BIT == 0) {
                        if (auto quotient = divide(right, pointerType->pointeeType()->size() / CHAR_BIT)) {
                            return std::make_unique<BinaryOperator>(
                                node->operatorKind(), std::move(typecast->operand()), std::move(quotient));
                        }
                    }
                }
            }
        }
        return nullptr;
    };

    switch (node->operatorKind()) {
        case BinaryOperator::ADD:
            if (auto result = rewritePointerArithmetic(node->left().get(), node->right().get())) {
                return simplify(std::move(result));
            }
            if (auto result = rewritePointerArithmetic(node->right().get(), node->left().get())) {
                return simplify(std::move(result));
            }
            break;
        case BinaryOperator::SUB:
            if (auto result = rewritePointerArithmetic(node->left().get(), node->right().get())) {
                return simplify(std::move(result));
            }
            break;
        default:
            break;
    }

    /*
     * Handle mathematical identities.
     */
    switch (node->operatorKind()) {
        case BinaryOperator::ADD: {
            if (isZero(node->left().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->right())));
            }
            if (isZero(node->right().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->left())));
            }
            break;
        }
        case BinaryOperator::SUB: {
            if (isZero(node->right().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->left())));
            }
            if (isZero(node->left().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<UnaryOperator>(
                    UnaryOperator::NEGATION,
                    std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->right()))));
            }
            break;
        }
        case BinaryOperator::MUL: {
            if (isOne(node->left().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->right())));
            }
            if (isOne(node->right().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->left())));
            }
            break;
        }
        case BinaryOperator::SHL:
        case BinaryOperator::SHR: {
            if (isZero(node->right().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->left())));
            }
            break;
        }
        case BinaryOperator::BITWISE_OR:
        case BinaryOperator::BITWISE_XOR:
        case BinaryOperator::LOGICAL_OR: {
            if (isZero(node->left().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->right())));
            }
            if (isZero(node->right().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->left())));
            }
            break;
        }
        case BinaryOperator::LOGICAL_AND: {
            if (isOne(node->right().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->left())));
            }
            if (isOne(node->left().get())) {
                auto type = typeCalculator_.getType(node.get());
                return simplify(std::make_unique<Typecast>(Typecast::STATIC_CAST, type, std::move(node->right())));
            }
            break;
        }
    }

    /* Simplifying boolean subexpressions. */
    switch (node->operatorKind()) {
        case BinaryOperator::LOGICAL_OR:
        case BinaryOperator::LOGICAL_AND: {
            node->left() = simplifyBooleanExpression(std::move(node->left()));
            node->right() = simplifyBooleanExpression(std::move(node->right()));
            break;
        }
    }

    /*
     * a + -1 -> a - 1
     * a - -1 -> a + 1
     */
    switch (node->operatorKind()) {
        case BinaryOperator::ADD: {
            if (auto constant = node->left()->as<IntegerConstant>()) {
                if (constant->type()->isSigned() && constant->value().size() > 1 && constant->value().signedValue() < 0) {
                    node->setOperatorKind(BinaryOperator::SUB);
                    constant->setValue(SizedValue(constant->value().size(), constant->value().absoluteValue()));
                }
            }
            if (auto constant = node->right()->as<IntegerConstant>()) {
                if (constant->type()->isSigned() && constant->value().size() > 1 && constant->value().signedValue() < 0) {
                    node->setOperatorKind(BinaryOperator::SUB);
                    constant->setValue(SizedValue(constant->value().size(), constant->value().absoluteValue()));
                }
            }
            break;
        }
        case BinaryOperator::SUB: {
            if (auto constant = node->right()->as<IntegerConstant>()) {
                if (constant->type()->isSigned() && constant->value().size() > 1 && constant->value().signedValue() < 0) {
                    node->setOperatorKind(BinaryOperator::ADD);
                    constant->setValue(SizedValue(constant->value().size(), constant->value().absoluteValue()));
                }
            }
            break;
        }
    }

    /*
     * Handling increments and decrements.
     *
     * x = x + 1; -> ++x;
     * x = x - 1; -> --x;
     */
    if (node->operatorKind() == BinaryOperator::ASSIGN) {
        /*
         * if the right hand side is a cast to the type of
         * the left hand side, check to see if the right hand side expression
         * will automatically be upgraded to the type of the left hand side
         * only works for integer types.
         */
        if (auto src = node->right()->as<Typecast>()) {
            auto destType = typeCalculator_.getType(node->left().get());
            auto cstType = typeCalculator_.getType(src->operand().get());
            if (destType->isInteger() && cstType->isInteger() && destType->size() >= cstType->size()) {
                if (destType->as<IntegerType>()->isSigned() == cstType->as<IntegerType>()->isSigned()) {
                    node->right() = std::move(src->operand());
                    return simplify(std::move(node));
                }
            }
        }
        if (VariableIdentifier *leftIdent = node->left()->as<VariableIdentifier>()) {
            if (BinaryOperator *binary = node->right()->as<BinaryOperator>()) {

                auto rewrite = [&](const Expression *left, const Expression *right) -> std::unique_ptr<Expression> {
                    if (auto rightIdent = left->as<VariableIdentifier>()) {
                        if (leftIdent->declaration() == rightIdent->declaration()) {
                            if (auto constant = right->as<IntegerConstant>()) {
                                if (constant->value().value() == 1) {
                                    return std::make_unique<UnaryOperator>(binary->operatorKind() == BinaryOperator::ADD
                                                                               ? UnaryOperator::PREFIX_INCREMENT
                                                                               : UnaryOperator::PREFIX_DECREMENT,
                                                                           std::move(node->left()));
                                } else if (constant->value().signedValue() == -1) {
                                    return std::make_unique<UnaryOperator>(binary->operatorKind() == BinaryOperator::ADD
                                                                               ? UnaryOperator::PREFIX_DECREMENT
                                                                               : UnaryOperator::PREFIX_INCREMENT,
                                                                           std::move(node->left()));
                                }
                            }
                        }
                    }
                    return nullptr;
                };
                if (binary->operatorKind() == BinaryOperator::ADD) {
                    if (auto result = rewrite(binary->left().get(), binary->right().get())) {
                        return result;
                    }
                    if (auto result = rewrite(binary->right().get(), binary->left().get())) {
                        return result;
                    }
                } else if (binary->operatorKind() == BinaryOperator::SUB) {
                    if (auto result = rewrite(binary->left().get(), binary->right().get())) {
                        return result;
                    }
                }
            }
        }
    }

    return std::move(node);
}

std::unique_ptr<CallOperator> Simplifier::simplify(std::unique_ptr<CallOperator> node) {
    node->callee() = simplify(std::move(node->callee()));
    node->arguments() = simplify(std::move(node->arguments()));
    return node;
}

std::unique_ptr<MemberAccessOperator> Simplifier::simplify(std::unique_ptr<MemberAccessOperator> node) {
    node->compound() = std::move(node->compound());
    return node;
}

std::unique_ptr<Expression> Simplifier::simplify(std::unique_ptr<Typecast> node) {
    node->operand() = simplify(std::move(node->operand()));

    /*
     * reinterpret_cast<int16_t>(*reinterpret_cast<uint16_t*>(&edi2))
     * will become *reinterpret_cast<int16_t*>(&edi2)
     */
    if (node->operand()->is<UnaryOperator>() &&
        node->operand()->as<UnaryOperator>()->operatorKind() == UnaryOperator::DEREFERENCE &&
        node->type()->isInteger()) {
        auto deref = node->operand()->as<UnaryOperator>();
        if (auto innerCast = deref->operand()->as<Typecast>()) {
            if (innerCast->type()->isPointer() && !node->type()->isPointer()) {
                auto ptrType = innerCast->type()->as<PointerType>();
                assert(ptrType);
                if (ptrType->pointeeType()->size() == node->type()->size() && ptrType->pointeeType()->isInteger()) {
                    deref->operand() = std::make_unique<Typecast>(
                        Typecast::REINTERPRET_CAST,
                        typeCalculator_.tree().makePointerType(innerCast->type()->size(), node->type()),
                        std::move(innerCast->operand()));
                    return simplify(std::move(node->operand()));
                }
            }
        }
    }
    /* Convert cast of pointer to a structure to a cast of pointer to its first field. */
    if (node->type()->isPointer() && !node->type()->isStructurePointer()) {
        if (auto pointerType = typeCalculator_.getType(node->operand().get())->as<PointerType>()) {
            if (const StructType *structType = pointerType->pointeeType()->as<StructType>()) {
                if (const MemberDeclaration *member = structType->getMember(0)) {
                    node->operand() = std::make_unique<UnaryOperator>(
                        UnaryOperator::REFERENCE,
                        std::make_unique<MemberAccessOperator>(MemberAccessOperator::ARROW,
                                                               std::move(node->operand()), member));
                }
            }
        }
    }

    /*
     * (int32_t*)(int64_t)expr -> (int32_t*)expr
     */
    if (node->type()->isScalar()) {
        if (auto typecast = node->operand()->as<Typecast>()) {
            auto operandType = typeCalculator_.getType(typecast->operand().get());

            if (typecast->type()->isScalar() &&
                operandType->isScalar() &&
                node->type()->size() == typecast->type()->size() &&
                typecast->type()->size() == operandType->size())
            {
                node->operand() = std::move(typecast->operand());
            }
        }
    }

    /* This really must be the last rule. */
    if (node->type() == typeCalculator_.getType(node->operand().get())) {
        return std::move(node->operand());
    }

    return std::move(node);
}

std::unique_ptr<Expression> Simplifier::simplify(std::unique_ptr<UnaryOperator> node) {
    node->operand() = simplify(std::move(node->operand()));

    if (node->operatorKind() == UnaryOperator::BITWISE_NOT &&
        typeCalculator_.getType(node->operand().get())->size() == 1) {
        node->setOperatorKind(UnaryOperator::LOGICAL_NOT);
    }

    switch (node->operatorKind()) {
        case UnaryOperator::DEREFERENCE: {
            if (auto unary = node->operand()->as<UnaryOperator>()) {
                if (unary->operatorKind() == UnaryOperator::REFERENCE) {
                    return std::move(unary->operand());
                }
            }
            if (auto binary = node->operand()->as<BinaryOperator>()) {
                if (binary->operatorKind() == BinaryOperator::ADD) {
                    if (typeCalculator_.getType(binary->left().get())->isPointer()) {
                        return std::make_unique<BinaryOperator>(BinaryOperator::ARRAY_SUBSCRIPT,
                                                                std::move(binary->left()), std::move(binary->right()));
                    } else if (typeCalculator_.getType(binary->right().get())->isPointer()) {
                        return std::make_unique<BinaryOperator>(BinaryOperator::ARRAY_SUBSCRIPT,
                                                                std::move(binary->right()), std::move(binary->left()));
                    }
                }
            }
            break;
        }
        case UnaryOperator::LOGICAL_NOT: {
            node->operand() = simplifyBooleanExpression(std::move(node->operand()));

            if (auto binary = node->operand()->as<BinaryOperator>()) {
                switch (binary->operatorKind()) {
                    case BinaryOperator::EQ:
                        binary->setOperatorKind(BinaryOperator::NEQ);
                        return std::move(node->operand());
                    case BinaryOperator::NEQ:
                        binary->setOperatorKind(BinaryOperator::EQ);
                        return std::move(node->operand());
                    case BinaryOperator::LT:
                        binary->setOperatorKind(BinaryOperator::GEQ);
                        return std::move(node->operand());
                    case BinaryOperator::LEQ:
                        binary->setOperatorKind(BinaryOperator::GT);
                        return std::move(node->operand());
                    case BinaryOperator::GT:
                        binary->setOperatorKind(BinaryOperator::LEQ);
                        return std::move(node->operand());
                    case BinaryOperator::GEQ:
                        binary->setOperatorKind(BinaryOperator::LT);
                        return std::move(node->operand());
                    default:
                        break;
                }
            }
            if (auto unary = node->operand()->as<UnaryOperator>()) {
                if (unary->operatorKind() == UnaryOperator::LOGICAL_NOT) {
                    if (typeCalculator_.getType(unary->operand().get())->size() == 1) {
                        return std::move(unary->operand());
                    }
                }
            }
            break;
        }
        default:
            break;
    }

    return std::move(node);
}

std::unique_ptr<Expression> Simplifier::simplifyBooleanExpression(
        std::unique_ptr<Expression> node, bool preserveEqualityComparison) {
    while (auto typecast = node->as<Typecast>()) {
        auto operandType = typeCalculator_.getType(typecast->operand().get());
        if (typecast->type()->isScalar() && operandType->isScalar() &&
            typecast->type()->size() >= operandType->size()) {
            node = std::move(typecast->operand());
        } else {
            break;
        }
    }

    if (auto unary1 = node->as<UnaryOperator>()) {
        if (unary1->operatorKind() == UnaryOperator::LOGICAL_NOT) {
            if (auto unary2 = unary1->operand()->as<UnaryOperator>()) {
                if (unary2->operatorKind() == UnaryOperator::LOGICAL_NOT) {
                    return simplifyBooleanExpression(
                        std::move(unary2->operand()), preserveEqualityComparison);
                }
            }
        }
    } else if (auto binary = node->as<BinaryOperator>()) {
        if (preserveEqualityComparison &&
            (binary->operatorKind() == BinaryOperator::EQ ||
             binary->operatorKind() == BinaryOperator::NEQ)) {
            return node;
        }
        if (binary->operatorKind() == BinaryOperator::NEQ) {
            if (isZero(binary->right().get())) {
                return simplifyBooleanExpression(std::move(binary->left()));
            }
            if (isZero(binary->left().get())) {
                return simplifyBooleanExpression(std::move(binary->right()));
            }
        } else if (binary->operatorKind() == BinaryOperator::EQ) {
            if (isZero(binary->right().get())) {
                return simplify(std::make_unique<UnaryOperator>(UnaryOperator::LOGICAL_NOT, std::move(binary->left())));
            }
            if (isZero(binary->left().get())) {
                return simplify(
                    std::make_unique<UnaryOperator>(UnaryOperator::LOGICAL_NOT, std::move(binary->right())));
            }
        }
    }

    return node;
}

std::unique_ptr<Statement> Simplifier::simplify(std::unique_ptr<Statement> node) {
    switch (node->statementKind()) {
        case Statement::BLOCK:
            return simplify(as<Block>(std::move(node)));
        case Statement::BREAK:
            return node;
        case Statement::CONTINUE:
            return node;
        case Statement::DO_WHILE:
            return simplify(as<DoWhile>(std::move(node)));
        case Statement::FOR:
            return simplify(as<For>(std::move(node)));
        case Statement::EXPRESSION_STATEMENT:
            return simplify(as<ExpressionStatement>(std::move(node)));
        case Statement::GOTO:
            return simplify(as<Goto>(std::move(node)));
        case Statement::IF:
            return simplify(as<If>(std::move(node)));
        case Statement::LABEL_STATEMENT:
            return simplify(as<LabelStatement>(std::move(node)));
        case Statement::RETURN:
            return simplify(as<Return>(std::move(node)));
        case Statement::WHILE:
            return simplify(as<While>(std::move(node)));
        case Statement::INLINE_ASSEMBLY:
            return node;
        case Statement::SWITCH:
            return simplify(as<Switch>(std::move(node)));
        case Statement::CASE_LABEL:
            return node;
        case Statement::DEFAULT_LABEL:
            return node;
    }
    unreachable();
}

std::unique_ptr<Block> Simplifier::simplify(std::unique_ptr<Block> node) {
    node->declarations() = simplify(std::move(node->declarations()));
    node->statements() = simplify(std::move(node->statements()));

    bool statementsChanged = false;
    bool changed;
    do {
        changed = false;
        while (inlineSingleUseTemporary(node.get(), node.get(), false,
                                        typeCalculator_)) {
            changed = true;
            statementsChanged = true;
        }
        while (removeDeadLocalAssignment(node.get())) {
            changed = true;
            statementsChanged = true;
        }
    } while (changed);

    /*
     * Temporary propagation and dead-assignment removal can leave an If
     * ladder in the exact form expected by the structured-control passes.
     * Give statements one more pass rather than making the printed output
     * depend on the form they had before block cleanup.
     */
    if (statementsChanged) {
        node->statements() = simplify(std::move(node->statements()));
    }

    recoverGuardedDoWhileForLoops(node.get(), typeCalculator_);
    recoverForLoops(node.get());
    pruneUnusedDeclarations(node.get());
    return node;
}

std::unique_ptr<DoWhile> Simplifier::simplify(std::unique_ptr<DoWhile> node) {
    node->condition() = simplifyBooleanExpression(simplify(std::move(node->condition())));
    node->body() = simplify(std::move(node->body()));
    return node;
}

std::unique_ptr<ExpressionStatement> Simplifier::simplify(std::unique_ptr<ExpressionStatement> node) {
    node->expression() = simplify(std::move(node->expression()));
    return node;
}

std::unique_ptr<For> Simplifier::simplify(std::unique_ptr<For> node) {
    node->initializer() = simplify(std::move(node->initializer()));
    node->condition() = simplifyBooleanExpression(simplify(std::move(node->condition())));
    node->increment() = simplify(std::move(node->increment()));
    node->body() = simplify(std::move(node->body()));
    return node;
}

std::unique_ptr<Goto> Simplifier::simplify(std::unique_ptr<Goto> node) {
    node->destination() = simplify(std::move(node->destination()));
    return node;
}

std::unique_ptr<Statement> Simplifier::simplify(std::unique_ptr<If> node) {
    /*
     * Recover switches compiled as a chain of equality/inequality tests.  Do
     * this before simplifying child statements so the longest outer chain is
     * considered before any of its suffixes.  Normalize only the conditions
     * first: otherwise harmless casts can hide the comparisons from the
     * matcher.  Keep comparisons against zero intact during this pass so they
     * can still become case 0.
     */
    If *conditional = node.get();
    while (conditional) {
        conditional->condition() = simplifyBooleanExpression(
            simplify(std::move(conditional->condition())), true);

        SwitchComparison comparison;
        if (!getSwitchComparison(conditional, comparison)) {
            break;
        }

        std::unique_ptr<Statement> *nonmatchingStatement = comparison.isEquality
            ? &conditional->elseStatement()
            : &conditional->thenStatement();
        bool invalidWrapper = false;
        conditional = getNestedIf(nonmatchingStatement->get(), invalidWrapper);
        if (invalidWrapper) {
            break;
        }
    }

    if (auto switchStatement = makeSwitchFromIfLadder(node)) {
        return simplify(std::move(switchStatement));
    }

    node->thenStatement() = simplify(std::move(node->thenStatement()));

    if (node->elseStatement()) {
        node->elseStatement() = simplify(std::move(node->elseStatement()));

        if (auto block = node->elseStatement()->as<Block>()) {
            if (block->statements().empty()) {
                node->elseStatement() = nullptr;
            }
        }

        if (node->elseStatement()) {
            if (auto block = node->thenStatement()->as<Block>()) {
                if (block->statements().empty()) {
                    node->thenStatement() = std::move(node->elseStatement());
                    node->condition() = simplify(
                        std::make_unique<UnaryOperator>(UnaryOperator::LOGICAL_NOT, std::move(node->condition())));
                }
            }
        }
    }

    /*
     * Simplifying a branch can expose the rest of a comparison ladder.  For
     * example, pruning an unused statement or declaration can turn a block
     * with several children into the one-If wrapper accepted by
     * getNestedIf().  The first (outermost-first) attempt above deliberately
     * runs before child simplification, so retry here before boolean
     * normalization changes comparisons against zero into !expressions.
     */
    if (auto switchStatement = makeSwitchFromIfLadder(node)) {
        return simplify(std::move(switchStatement));
    }

    node->condition() = simplifyBooleanExpression(simplify(std::move(node->condition())));

    return node;
}

std::unique_ptr<LabelStatement> Simplifier::simplify(std::unique_ptr<LabelStatement> node) {
    if (node->identifier()->declaration()->referenceCount() == 0) {
        return nullptr;
    }
    return node;
}

std::unique_ptr<Return> Simplifier::simplify(std::unique_ptr<Return> node) {
    if (node->returnValue()) {
        node->returnValue() = simplify(std::move(node->returnValue()));
    }
    return node;
}

std::unique_ptr<While> Simplifier::simplify(std::unique_ptr<While> node) {
    node->condition() = simplifyBooleanExpression(simplify(std::move(node->condition())));
    node->body() = simplify(std::move(node->body()));
    return node;
}

std::unique_ptr<Switch> Simplifier::simplify(std::unique_ptr<Switch> node) {
    node->expression() = simplifyBooleanExpression(simplify(std::move(node->expression())));
    node->body() = simplify(std::move(node->body()));
    return node;
}

template<class T>
std::vector<T> Simplifier::simplify(std::vector<T> range) {
    foreach (auto &item, range) {
        item = simplify(std::move(item));
    }
    range.erase(std::remove_if(range.begin(), range.end(), IsNull()), range.end());
    return range;
}

} // namespace likec
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
