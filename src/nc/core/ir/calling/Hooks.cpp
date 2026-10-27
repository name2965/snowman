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

#include "Hooks.h"

#include <cassert>

#include <nc/common/Foreach.h>
#include <nc/common/Range.h>
#include <nc/common/make_unique.h>

#include <nc/core/arch/Instruction.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/Utils.h>
#include <nc/core/ir/dflow/Value.h>

#include "Conventions.h"
#include "CallHook.h"
#include "Convention.h"
#include "EntryHook.h"
#include "Signatures.h"
#include "ReturnHook.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

/** Reads in-progress lattice facts for instrumentation callbacks only. */
CalleeId getProvisionalCalleeId(const Call *call,
                                const dflow::Dataflow &dataflow) {
    assert(call != nullptr);
    assert(dataflow.running());

    const dflow::Value *targetValue = dataflow.findValue(call->target());
    if (targetValue && targetValue->abstractValue().isConcrete()) {
        return EntryAddress(
            targetValue->abstractValue().asConcrete().value());
    }
    if (call->instruction()) {
        return CallAddress(call->instruction()->addr());
    }
    return CalleeId();
}

bool hasProvisionalConcreteCallee(const Call *call,
                                  const dflow::Dataflow &dataflow) {
    assert(call != nullptr);
    assert(dataflow.running());

    const dflow::Value *targetValue = dataflow.findValue(call->target());
    return targetValue && targetValue->abstractValue().isConcrete();
}

bool isProvisionalReturnAddress(const Term *term,
                                const dflow::Dataflow &dataflow) {
    assert(term != nullptr);
    assert(dataflow.running());

    const dflow::Value *value = dataflow.findValue(term);
    return value && value->isReturnAddress();
}

bool isProvisionalReturn(const Jump *jump,
                         const dflow::Dataflow &dataflow) {
    assert(jump != nullptr);
    const auto isReturnTarget = [&dataflow](const JumpTarget &target) {
        return target.address() &&
            isProvisionalReturnAddress(target.address(), dataflow);
    };
    return isReturnTarget(jump->thenTarget()) ||
        isReturnTarget(jump->elseTarget());
}

} // anonymous namespace

Hooks::Hooks(const Conventions &conventions, const Signatures &signatures):
    conventions_(conventions), signatures_(signatures)
{}

Hooks::~Hooks() {}

const Convention *Hooks::getConvention(const CalleeId &calleeId) const {
    if (!calleeId) {
        return nullptr;
    }
    if (auto result = conventions_.getConvention(calleeId)) {
        return result;
    } else {
        conventionDetector_(calleeId);
        return conventions_.getConvention(calleeId);
    }
}

const EntryHook *Hooks::getEntryHook(const Function *function) const {
    assert(function != nullptr);

    return nc::find(lastEntryHooks_, function);
}

const CallHook *Hooks::getCallHook(const Call *call) const {
    assert(call != nullptr);

    return nc::find(lastCallHooks_, call);
}

const ReturnHook *Hooks::getReturnHook(const Jump *jump) const {
    assert(jump != nullptr);

    return nc::find(lastReturnHooks_, jump);
}

void Hooks::instrument(Function *function, const dflow::Dataflow *dataflow) {
    assert(function != nullptr);
    assert(dataflow != nullptr);

    deinstrument(function);

    if (function->entry()) {
        function2callback_[function] = function->entry()->pushFront(std::make_unique<Callback>([=](){
            instrumentEntry(function);
        }));
    }

    foreach (auto basicBlock, function->basicBlocks()) {
        foreach (auto statement, basicBlock->statements()) {
            if (auto call = statement->as<Call>()) {
                call2callback_[call] = basicBlock->insertAfter(call, std::make_unique<Callback>([=](){
                    instrumentCall(call, *dataflow, true);
                }));
            } else if (auto jump = statement->as<Jump>()) {
                jump2callback_[jump] = basicBlock->insertBefore(jump, std::make_unique<Callback>([=](){
                    if (isProvisionalReturn(jump, *dataflow)) {
                        instrumentReturn(jump);
                    } else {
                        deinstrumentReturn(jump);
                    }
                }));
            }
        }
    }
}

void Hooks::finalizeInstrumentation(Function *function,
                                    dflow::Dataflow &dataflow) {
    assert(function != nullptr);
    assert(!dataflow.running());

    if (dataflow.incomplete()) {
        std::vector<Call *> calls;
        foreach (const auto &callAndCallback, call2callback_) {
            Call *call = callAndCallback.first;
            if (call->basicBlock() &&
                call->basicBlock()->function() == function)
            {
                calls.push_back(call);
            }
        }
        foreach (Call *call, calls) {
            /* A replacement hook would introduce fresh terms after the last
             * dataflow pass. Retain already analyzed call-site hooks, but
             * remove hooks whose ABI contract came from an unfinished
             * resolved-target fact. */
            if (nc::find(provisionalCallHooks_, call)) {
                deinstrumentCall(call);
            }
        }

        std::vector<Jump *> jumps;
        foreach (const auto &jumpAndCallback, jump2callback_) {
            Jump *jump = jumpAndCallback.first;
            if (jump->basicBlock() &&
                jump->basicBlock()->function() == function)
            {
                jumps.push_back(jump);
            }
        }
        foreach (Jump *jump, jumps) {
            deinstrumentReturn(jump);
        }
    }

    /* Hook replacement happens after DataflowAnalyzer's regular cleanup. */
    dataflow.discardDetachedFacts();
}

void Hooks::deinstrument(Function *function) {
    assert(function != nullptr);

    if (auto callback = nc::find(function2callback_, function)) {
        deinstrumentEntry(function);
        callback->basicBlock()->erase(callback);
        function2callback_.erase(function);
    }

    foreach (auto basicBlock, function->basicBlocks()) {
        foreach (auto statement, basicBlock->statements()) {
            if (auto call = statement->as<Call>()) {
                if (auto callback = nc::find(call2callback_, call)) {
                    deinstrumentCall(call);
                    callback->basicBlock()->erase(callback);
                    call2callback_.erase(call);
                }
            } else if (auto jump = statement->as<Jump>()) {
                if (auto callback = nc::find(jump2callback_, jump)) {
                    deinstrumentReturn(jump);
                    callback->basicBlock()->erase(callback);
                    jump2callback_.erase(jump);
                }
            }
        }
    }
}

void Hooks::instrumentEntry(Function *function) {
    auto convention = getConvention(getCalleeId(function));
    auto signature = signatures_.getSignature(function).get();
    auto &entryHook = entryHooks_[std::make_tuple(function, convention, signature)];

    if (!entryHook) {
        entryHook = std::make_unique<EntryHook>(convention, signature);
    }

    auto &lastEntryHook = lastEntryHooks_[function];

    if (entryHook.get() != lastEntryHook) {
        if (lastEntryHook) {
            lastEntryHook->patch().remove();
        }
        if (entryHook) {
            auto callback = nc::find(function2callback_, function);
            entryHook->patch().insertAfter(callback);
        }
        lastEntryHook = entryHook.get();
    }
}

void Hooks::deinstrumentEntry(Function *function) {
    auto &lastEntryHook = lastEntryHooks_[function];

    if (lastEntryHook) {
        lastEntryHook->patch().remove();
        lastEntryHook = nullptr;
    }
}

void Hooks::instrumentCall(Call *call, const dflow::Dataflow &dataflow,
                           bool useProvisionalFacts) {
    assert(!useProvisionalFacts || dataflow.running());
    const CalleeId calleeId = useProvisionalFacts ?
        getProvisionalCalleeId(call, dataflow) :
        getCalleeId(call, dataflow);
    const bool hasProvisionalCallee = useProvisionalFacts &&
        hasProvisionalConcreteCallee(call, dataflow);
    CalleeId callSiteId;
    if (call->instruction()) {
        callSiteId = CalleeId(CallAddress(call->instruction()->addr()));
    }

    /* A call instruction may carry a stronger contract than its resolved
     * address (for example, an IAT entry forwarded to a shared implementation
     * address). Never let that per-call fact leak to another call which
     * happens to resolve to the same address. */
    const Convention *convention = callSiteId ?
        conventions_.getConvention(callSiteId) : nullptr;
    const bool hasCallSiteConvention = convention != nullptr;
    if (!convention) {
        convention = getConvention(calleeId);
    }
    if (!convention) {
        deinstrumentCall(call);
        return;
    }
    auto signature = signatures_.getSignature(call).get();
    auto stackArgumentsSize = hasCallSiteConvention ?
        conventions_.getStackArgumentsSize(callSiteId) :
        conventions_.getStackArgumentsSize(calleeId);
    boost::optional<ByteSize> stackCleanupSize;
    bool unknownStackCleanup = false;
    const auto returnCleanup = hasCallSiteConvention ?
        conventions_.getReturnStackCleanup(callSiteId) :
        conventions_.getReturnStackCleanup(calleeId);
    if (returnCleanup.isExact()) {
        stackCleanupSize = returnCleanup.size();
    } else if (returnCleanup.isConflicting()) {
        unknownStackCleanup = true;
    } else if (convention->calleeCleanup()) {
        stackCleanupSize = stackArgumentsSize;
    }
    auto &callHook = callHooks_[std::make_tuple(
        call, convention, signature, stackCleanupSize, unknownStackCleanup)];

    if (!callHook) {
        callHook = std::make_unique<CallHook>(
            convention, signature, stackCleanupSize, unknownStackCleanup);
    }

    auto &lastCallHook = lastCallHooks_[call];

    if (callHook.get() != lastCallHook) {
        if (lastCallHook) {
            lastCallHook->patch().remove();
        }
        if (callHook) {
            auto callback = nc::find(call2callback_, call);
            callHook->patch().insertAfter(callback);
        }
        lastCallHook = callHook.get();
    }
    provisionalCallHooks_[call] =
        hasProvisionalCallee && !hasCallSiteConvention;
}

void Hooks::deinstrumentCall(Call *call) {
    auto &lastCallHook = lastCallHooks_[call];

    if (lastCallHook) {
        lastCallHook->patch().remove();
        lastCallHook = nullptr;
    }
    provisionalCallHooks_.erase(call);
}

void Hooks::instrumentReturn(Jump *jump) {
    auto function = jump->basicBlock()->function();
    auto convention = getConvention(getCalleeId(function));
    if (!convention) {
        deinstrumentReturn(jump);
        return;
    }
    auto signature = signatures_.getSignature(function).get();
    auto &returnHook = returnHooks_[std::make_tuple(jump, convention, signature)];

    if (!returnHook) {
        returnHook = std::make_unique<ReturnHook>(convention, signature);
    }

    auto &lastReturnHook = lastReturnHooks_[jump];

    if (returnHook.get() != lastReturnHook) {
        if (lastReturnHook) {
            lastReturnHook->patch().remove();
        }
        if (returnHook) {
            auto callback = nc::find(jump2callback_, jump);
            returnHook->patch().insertAfter(callback);
        }
        lastReturnHook = returnHook.get();
    }
}

void Hooks::deinstrumentReturn(Jump *jump) {
    auto &lastReturnHook = lastReturnHooks_[jump];

    if (lastReturnHook) {
        lastReturnHook->patch().remove();
        lastReturnHook = nullptr;
    }
}

CalleeId getCalleeId(const Function *function) {
    assert(function != nullptr);

    if (function->entry() && function->entry()->address()) {
        return CalleeId(EntryAddress(*function->entry()->address()));
    } else {
        return CalleeId(function);
    }
}

CalleeId getCalleeId(const Call *call, const dflow::Dataflow &dataflow) {
    assert(call != nullptr);

    const dflow::Value *targetValue = dataflow.converged() ?
        dataflow.findValue(call->target()) : nullptr;
    if (targetValue && targetValue->abstractValue().isConcrete()) {
        return EntryAddress(
            targetValue->abstractValue().asConcrete().value());
    }
    if (call->instruction()) {
        return CallAddress(call->instruction()->addr());
    }
    return CalleeId();
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
