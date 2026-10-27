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

#include "LivenessAnalyzer.h"

#include <cassert>
#include <functional>

#include <nc/common/Foreach.h>

#include <nc/core/arch/Architecture.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/MemoryDomain.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallHook.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/ReturnHook.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cflow/BasicNode.h>
#include <nc/core/ir/cflow/Graph.h>
#include <nc/core/ir/cflow/Switch.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/dflow/Value.h>

#include "Liveness.h"

namespace nc {
namespace core {
namespace ir {
namespace liveness {

LivenessAnalyzer::LivenessAnalyzer(Liveness &liveness, const Function *function,
    const dflow::Dataflow &dataflow, const arch::Architecture *architecture,
    const cflow::Graph *regionGraph, const calling::Hooks &hooks,
    const calling::Signatures *signatures, const LogToken &log
):
    liveness_(liveness), function_(function), dataflow_(dataflow),
    architecture_(architecture), regionGraph_(regionGraph), hooks_(hooks),
    signatures_(signatures), log_(log)
{}

void LivenessAnalyzer::analyze() {
    if (!dataflow_.converged()) {
        /* Fail closed.  Definition elimination and expression substitution
         * consume this liveness result, so a bounded intermediate dataflow
         * state must not make any IR value disappear. */
        std::function<void(const Term *)> makeTreeLive =
            [&](const Term *term) {
                if (!term) {
                    return;
                }
                makeLive(term);
                term->callOnChildren(makeTreeLive);
            };

        foreach (const BasicBlock *basicBlock, function_->basicBlocks()) {
            foreach (const Statement *statement, basicBlock->statements()) {
                if (const Assignment *assignment = statement->asAssignment()) {
                    makeTreeLive(assignment->left());
                    makeTreeLive(assignment->right());
                } else if (const Jump *jump = statement->asJump()) {
                    makeTreeLive(jump->condition());
                    makeTreeLive(jump->thenTarget().address());
                    makeTreeLive(jump->elseTarget().address());
                } else if (const Call *call = statement->asCall()) {
                    makeTreeLive(call->target());
                } else if (const Touch *touch = statement->asTouch()) {
                    makeTreeLive(touch->term());
                } else if (const TrackedMemoryInvalidation *invalidation =
                               statement->as<TrackedMemoryInvalidation>()) {
                    foreach (const auto &candidate,
                             invalidation->pointerCandidates()) {
                        makeTreeLive(candidate.get());
                    }
                }
            }
        }
        return;
    }

    computeInvisibleJumps();

    foreach (const BasicBlock *basicBlock, function_->basicBlocks()) {
        foreach (const Statement *statement, basicBlock->statements()) {
            computeLiveness(statement);
        }
    }
}

void LivenessAnalyzer::computeInvisibleJumps() {
    if (!regionGraph_) {
        return;
    }

    invisibleJumps_.clear();

    foreach (auto node, regionGraph_->nodes()) {
        if (auto region = node->as<cflow::Region>()) {
            if (auto witch = region->as<cflow::Switch>()) {
                if (witch->boundsCheckNode()) {
                    invisibleJumps_.push_back(witch->boundsCheckNode()->basicBlock()->getJump());
                }
                foreach (const cflow::BasicNode *dispatch,
                         witch->dispatchNodes()) {
                    invisibleJumps_.push_back(
                        dispatch->basicBlock()->getJump());
                }
                makeLive(witch->switchTerm());
            }
        }
    }

    std::sort(invisibleJumps_.begin(), invisibleJumps_.end());
}

void LivenessAnalyzer::computeLiveness(const Statement *statement) {
    switch (statement->kind()) {
        case Statement::INLINE_ASSEMBLY:
            break;
        case Statement::ASSIGNMENT: {
            auto assignment = statement->asAssignment();
            auto memoryLocation = dataflow_.getMemoryLocation(assignment->left());

            if (!memoryLocation || architecture_->isGlobalMemory(memoryLocation)) {
                makeLive(assignment->left());
            }
            break;
        }
        case Statement::JUMP: {
            const Jump *jump = statement->asJump();

            if (!std::binary_search(invisibleJumps_.begin(), invisibleJumps_.end(), jump)) {
                if (jump->condition()) {
                    makeLive(jump->condition());
                }
                if (jump->thenTarget().address() && !dflow::isReturnAddress(jump->thenTarget(), dataflow_)) {
                    makeLive(jump->thenTarget().address());
                }
                if (jump->elseTarget().address() && !dflow::isReturnAddress(jump->elseTarget(), dataflow_)) {
                    makeLive(jump->elseTarget().address());
                }

                if (signatures_ && dflow::isReturn(jump, dataflow_)) {
                    if (auto signature = signatures_->getSignature(function_)) {
                        if (signature->returnValue()) {
                            if (auto returnHook = hooks_.getReturnHook(jump)) {
                                makeLive(returnHook->getReturnValueTerm(signature->returnValue().get()));
                            }
                        }
                    }
                }
            }
            break;
        }
        case Statement::CALL: {
            const Call *call = statement->asCall();

            makeLive(call->target());

            const calling::CallHook *callHook = hooks_.getCallHook(call);
            auto makeSnapshotMemoryDefinitionsLive =
                [&](const Statement *snapshot, bool includeStack,
                    bool includeOtherMemory) {
                    assert(snapshot != nullptr);
                    foreach (const auto &chunk,
                             dataflow_.getDefinitions(snapshot).chunks()) {
                        const Domain domain = chunk.location().domain();
                        const bool isRegister =
                            domain >= MemoryDomain::FIRST_REGISTER &&
                            domain <= MemoryDomain::LAST_REGISTER;
                        if (!isRegister &&
                            ((domain == MemoryDomain::STACK && includeStack) ||
                             (domain != MemoryDomain::STACK &&
                              includeOtherMemory)))
                        {
                            foreach (const Term *definition,
                                     chunk.definitions()) {
                                makeLive(definition);
                            }
                        }
                    }
                };

            bool hasSignature = false;
            if (signatures_) {
                if (auto signature = signatures_->getSignature(call)) {
                    hasSignature = true;
                    if (callHook) {
                        const auto &prototype = signature->prototype();
                        const bool completePrototype = prototype &&
                            prototype->memoryEffectsAreComplete() &&
                            prototype->parameters().size() ==
                                signature->arguments().size();

                        /* An inferred prototype is not a complete effect
                         * contract. Preserve all pre-effect non-register
                         * memory;
                         * A declaration without an explicit complete-effect
                         * promise and a parameter-count mismatch are
                         * incomplete too.
                         * Exact prototypes can retain the per-argument test. */
                        bool mayReadStackPointee = !completePrototype;
                        bool mayReadOtherPointee = !completePrototype;
                        std::size_t argumentIndex = 0;
                        foreach (const auto &argument, signature->arguments()) {
                            const Term *argumentTerm =
                                callHook->getArgumentTerm(argument.get());
                            assert(argumentTerm != nullptr);
                            makeLive(argumentTerm);

                            const bool mayReadPointee =
                                !completePrototype ||
                                prototype->parameters()[argumentIndex]
                                    .mayReadMemory();
                            if (mayReadPointee) {
                                const dflow::Value *value =
                                    dataflow_.findValue(argumentTerm);
                                if (!value || value->mayBeStackOffset()) {
                                    mayReadStackPointee = true;
                                }
                                if (!value || !value->isStackOffset()) {
                                    mayReadOtherPointee = true;
                                }
                            }
                            ++argumentIndex;
                        }

                        if (mayReadStackPointee || mayReadOtherPointee) {
                            const Statement *snapshot =
                                callHook->pointeeReadSnapshotStatement();
                            assert(snapshot != nullptr);
                            makeSnapshotMemoryDefinitionsLive(
                                snapshot, mayReadStackPointee,
                                mayReadOtherPointee);
                        }
                    }
                }
            }

            /* The first analysis pass has no reconstructed signature yet.
             * Its inference snapshot is the only sound pre-call boundary, so
             * do not eliminate any tracked non-register definition reaching
             * it. */
            if (!hasSignature && callHook && callHook->snapshotStatement()) {
                makeSnapshotMemoryDefinitionsLive(
                    callHook->snapshotStatement(), true, true);
            }

            break;
        }
        case Statement::HALT:
            break;
        case Statement::TOUCH:
            break;
        case Statement::CALLBACK:
            break;
        case Statement::REMEMBER_REACHING_DEFINITIONS:
            break;
        case Statement::TRACKED_MEMORY_INVALIDATION:
            break;
        default:
            log_.warning(tr("%1: Unknown statement kind: %2.").arg(Q_FUNC_INFO).arg(statement->kind()));
            break;
    }
}

void LivenessAnalyzer::propagateLiveness(const Term *term) {
    assert(term != nullptr);

#ifdef NC_PREFER_CONSTANTS_TO_EXPRESSIONS
    const dflow::Value *value = dataflow_.findValue(term);
    if (dataflow_.converged() && term->isRead() && value &&
        value->abstractValue().isConcrete()) {
        return;
    }
#endif

    switch (term->kind()) {
        case Term::INT_CONST:
            break;
        case Term::INTRINSIC:
            break;
        case Term::MEMORY_LOCATION_ACCESS: {
            if (term->isRead()) {
                foreach (auto &chunk, dataflow_.getDefinitions(term).chunks()) {
                    foreach (const Term *definition, chunk.definitions()) {
                        makeLive(definition);
                    }
                }
            } else if (term->isWrite()) {
                if (auto source = term->source()) {
                    makeLive(source);
                }
            }
            break;
        }
        case Term::DEREFERENCE: {
            if (term->isRead()) {
                foreach (auto &chunk, dataflow_.getDefinitions(term).chunks()) {
                    foreach (const Term *definition, chunk.definitions()) {
                        makeLive(definition);
                    }
                }
            } else if (term->isWrite()) {
                if (auto source = term->source()) {
                    makeLive(source);
                }
            }

            if (!dataflow_.getMemoryLocation(term)) {
                makeLive(term->asDereference()->address());
            }
            break;
        }
        case Term::UNARY_OPERATOR: {
            const UnaryOperator *unary = term->asUnaryOperator();
            makeLive(unary->operand());
            break;
        }
        case Term::BINARY_OPERATOR: {
            const BinaryOperator *binary = term->asBinaryOperator();
            makeLive(binary->left());
            makeLive(binary->right());
            break;
        }
        default:
            log_.warning(tr("%1: Unknown term kind: %2.").arg(Q_FUNC_INFO).arg(term->kind()));
            break;
    }
}

void LivenessAnalyzer::makeLive(const Term *term) {
    assert(term != nullptr);
    if (!liveness_.isLive(term)) {
        liveness_.makeLive(term);
        propagateLiveness(term);
    }
}

} // namespace liveness
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
