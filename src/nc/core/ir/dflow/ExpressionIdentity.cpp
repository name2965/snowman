/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "ExpressionIdentity.h"

#include <cstddef>
#include <set>

#include <nc/core/ir/MemoryDomain.h>
#include <nc/core/ir/Terms.h>

#include "Dataflow.h"
#include "DefUseGraph.h"
#include "ValueProvenance.h"

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
        return term->is<MemoryLocationAccess>();
    }

    /* Dataflow turns a dereference with a single, stable effective address
     * into an exact STACK location.  Such a read can participate in an
     * identity proof, but only through its reaching definition below.  Do
     * not extend this to the generic MEMORY domain: globals and unresolved
     * pointers may be externally mutable (or volatile). */
    return location && location.domain() == MemoryDomain::STACK &&
        (term->is<MemoryLocationAccess>() || term->is<Dereference>());
}

bool isCommutative(int operatorKind) {
    switch (operatorKind) {
        case BinaryOperator::ADD:
        case BinaryOperator::AND:
        case BinaryOperator::OR:
        case BinaryOperator::XOR:
        case BinaryOperator::EQUAL:
        case BinaryOperator::MUL:
            return true;

        default:
            return false;
    }
}

struct TermPair {
    const Term *left;
    const Term *right;
};

/* std::less supplies a strict total order for unrelated pointers. */
struct TermPairLess {
    bool operator()(const TermPair &first, const TermPair &second) const {
        std::less<const Term *> less;
        if (less(first.left, second.left)) {
            return true;
        }
        if (less(second.left, first.left)) {
            return false;
        }
        return less(first.right, second.right);
    }
};

class Comparison {
    static const std::size_t MAX_IDENTITY_DEPTH = 64;

    const Dataflow &dataflow_;
    const DefUseGraph &defUse_;
    std::set<TermPair, TermPairLess> visiting_;

public:
    Comparison(const Dataflow &dataflow, const DefUseGraph &defUse):
        dataflow_(dataflow), defUse_(defUse)
    {}

    bool compare(const Term *left, const Term *right, std::size_t depth) {
        if (!left || !right || !left->statement() || !right->statement() ||
            left->size() != right->size() || left->kind() != right->kind() ||
            depth > MAX_IDENTITY_DEPTH)
        {
            return false;
        }

        const TermPair pair{left, right};
        const TermPair reversePair{right, left};
        if (visiting_.find(pair) != visiting_.end() ||
            visiting_.find(reversePair) != visiting_.end())
        {
            return false;
        }
        visiting_.insert(pair);

        struct EraseOnReturn {
            std::set<TermPair, TermPairLess> &set;
            TermPair pair;
            ~EraseOnReturn() { set.erase(pair); }
        } eraseOnReturn{visiting_, pair};

        switch (left->kind()) {
            case Term::INT_CONST:
                return left->asConstant()->value().value() ==
                       right->asConstant()->value().value();

            case Term::INTRINSIC:
                /* Intrinsics can denote dynamic/nondeterministic values.  A
                 * matching kind or spelling therefore does not prove value
                 * identity; only the same IR occurrence does. */
                return left == right;

            case Term::DEREFERENCE:
                return compareTrackedReads(left, right);

            case Term::MEMORY_LOCATION_ACCESS:
                return compareTrackedReads(left, right);

            case Term::UNARY_OPERATOR: {
                const UnaryOperator *leftUnary = left->asUnaryOperator();
                const UnaryOperator *rightUnary = right->asUnaryOperator();
                return leftUnary->operatorKind() ==
                           rightUnary->operatorKind() &&
                       compare(leftUnary->operand(), rightUnary->operand(),
                               depth + 1);
            }

            case Term::BINARY_OPERATOR: {
                const BinaryOperator *leftBinary = left->asBinaryOperator();
                const BinaryOperator *rightBinary = right->asBinaryOperator();
                if (leftBinary->operatorKind() !=
                    rightBinary->operatorKind())
                {
                    return false;
                }

                if (compare(leftBinary->left(), rightBinary->left(),
                            depth + 1) &&
                    compare(leftBinary->right(), rightBinary->right(),
                            depth + 1))
                {
                    return true;
                }

                return isCommutative(leftBinary->operatorKind()) &&
                    compare(leftBinary->left(), rightBinary->right(),
                            depth + 1) &&
                    compare(leftBinary->right(), rightBinary->left(),
                            depth + 1);
            }
        }

        return false;
    }

private:
    bool compareTrackedReads(const Term *left, const Term *right) const {
        if (!left->isRead() || !right->isRead()) {
            return false;
        }

        const MemoryLocation &leftLocation =
            dataflow_.getMemoryLocation(left);
        const MemoryLocation &rightLocation =
            dataflow_.getMemoryLocation(right);
        if (!isTrackedScalarLocation(left, leftLocation) ||
            !isTrackedScalarLocation(right, rightLocation) ||
            leftLocation != rightLocation)
        {
            return false;
        }

        const DefUseGraph::DefinitionSet &leftDefinitions =
            defUse_.definitions(left);
        const DefUseGraph::DefinitionSet &rightDefinitions =
            defUse_.definitions(right);

        const Term *leftDefinition = leftDefinitions.uniqueDefinition();
        const Term *rightDefinition = rightDefinitions.uniqueDefinition();
        return leftDefinitions.isComplete() &&
            rightDefinitions.isComplete() &&
            leftDefinitions.location() == leftLocation &&
            rightDefinitions.location() == rightLocation &&
            leftDefinition && leftDefinition == rightDefinition &&
            dataflow_.getMemoryLocation(leftDefinition) == leftLocation;
    }
};

const std::size_t Comparison::MAX_IDENTITY_DEPTH;

} // anonymous namespace

bool ExpressionIdentity::areIdentical(const Term *left,
                                      const Term *right) const {
    /* Refuse results from a partial abstract-interpretation iteration. */
    if (!dataflow_.converged() || !left || !right ||
        !provenance_.isPathComplete(left) ||
        !provenance_.isPathComplete(right))
    {
        return false;
    }

    Comparison comparison(dataflow_, defUse_);
    return comparison.compare(left, right, 0);
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
