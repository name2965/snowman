/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "ExpressionEffects.h"

#include <cassert>

#include <nc/core/ir/MemoryLocation.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/dflow/Dataflow.h>

namespace nc {
namespace core {
namespace ir {
namespace effects {

namespace {

bool isRegisterLocation(const MemoryLocation &location) {
    return location &&
        location.domain() >= MemoryDomain::FIRST_REGISTER &&
        location.domain() <= MemoryDomain::LAST_REGISTER;
}

} // anonymous namespace

ExpressionEffects ExpressionEffects::analyzeImpl(
        const Term *term, const dflow::Dataflow &dataflow) {
    assert(term != nullptr);

    ExpressionEffects result;
    switch (term->kind()) {
        case Term::INT_CONST:
            break;

        case Term::INTRINSIC:
            result.setNonrepeatable();
            break;

        case Term::MEMORY_LOCATION_ACCESS:
            if (!term->isRead() ||
                !isRegisterLocation(dataflow.getMemoryLocation(term)))
            {
                result.setReadsObservableState();
            }
            break;

        case Term::DEREFERENCE:
            result.merge(analyzeImpl(
                term->asDereference()->address(), dataflow));
            result.setReadsObservableState();
            result.setMayTrap();
            break;

        case Term::UNARY_OPERATOR:
            result.merge(analyzeImpl(
                term->asUnaryOperator()->operand(), dataflow));
            break;

        case Term::BINARY_OPERATOR: {
            const BinaryOperator *binary = term->asBinaryOperator();
            result.merge(analyzeImpl(binary->left(), dataflow));
            result.merge(analyzeImpl(binary->right(), dataflow));
            switch (binary->operatorKind()) {
                case BinaryOperator::SIGNED_DIV:
                case BinaryOperator::SIGNED_REM:
                case BinaryOperator::UNSIGNED_DIV:
                case BinaryOperator::UNSIGNED_REM:
                    result.setMayTrap();
                    break;
                default:
                    break;
            }
            break;
        }
    }
    return result;
}

ExpressionEffects ExpressionEffects::analyze(
        const Term *term, const dflow::Dataflow &dataflow) {
    assert(term != nullptr);
    return analyzeImpl(term, dataflow);
}

} // namespace effects
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
