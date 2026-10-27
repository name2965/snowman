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

#include "CallHook.h"

#include <nc/common/Foreach.h>
#include <nc/common/make_unique.h>

#include <nc/core/ir/MemoryDomain.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>

#include "CallSignature.h"
#include "Convention.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

CallHook::CallHook(const Convention *convention, const CallSignature *signature,
    const boost::optional<ByteSize> &stackCleanupSize,
    bool unknownStackCleanup, bool signatureIsInferred):
    stackPointer_(nullptr), snapshotStatement_(nullptr),
    pointeeReadSnapshotStatement_(nullptr),
    argumentObservation_(ArgumentObservation::NONE)
{
    assert(convention != nullptr);

    auto &statements = patch_.statements();

    if (convention->stackPointer()) {
        auto stackPointer = std::make_unique<MemoryLocationAccess>(convention->stackPointer());
        stackPointer_ = stackPointer.get();

        statements.push_back(std::make_unique<Touch>(
            std::move(stackPointer),
            Term::READ
        ));
    }

    auto addArgumentRead = [&](std::unique_ptr<Term> term) {
        statements.push_back(std::make_unique<Touch>(
            std::move(term),
            Term::READ
        ));
    };

    auto addReturnValueWrite = [&](std::unique_ptr<Term> term) {
        auto size = term->size();
        statements.push_back(std::make_unique<Assignment>(
            std::move(term),
            std::make_unique<Intrinsic>(Intrinsic::UNDEFINED, size)
        ));
    };

    auto addCallClobbers = [&]() {
        foreach (const MemoryLocation &location,
                 convention->clobberedLocations()) {
            addReturnValueWrite(
                std::make_unique<MemoryLocationAccess>(location));
        }
    };

    if (signature) {
        std::vector<std::unique_ptr<Term>> pointerCandidates;
        pointerCandidates.reserve(signature->arguments().size());
        const auto &prototype = signature->prototype();
        const bool completePrototype = prototype &&
            !prototype->variadic() &&
            prototype->memoryEffectsAreComplete() &&
            prototype->parameters().size() == signature->arguments().size();
        if (signatureIsInferred) {
            argumentObservation_ = ArgumentObservation::ALL;
        } else if (prototype && prototype->variadic()) {
            argumentObservation_ = ArgumentObservation::VARIADIC_TAIL;
        }

        /* An inferred signature identifies observed argument locations, but it
         * is not a complete memory-effect contract. Hidden arguments and
         * previously escaped pointers therefore require a conservative
         * pre-effect snapshot and whole-memory barrier. A parameter-count
         * declaration without an explicit complete-effect promise and a
         * parameter-count mismatch are incomplete as well: treating either
         * as exact could silently miss pointee effects. */
        bool hasPointeeReadEffect = !completePrototype;

        std::size_t argumentIndex = 0;
        foreach (const auto &term, signature->arguments()) {
            auto clone = term->clone();
            const Term *clonePointer = clone.get();
            const bool mayReadMemory = !completePrototype ||
                prototype->parameters()[argumentIndex].mayReadMemory();
            const bool mayWriteMemory = completePrototype &&
                prototype->parameters()[argumentIndex].mayWriteMemory();
            hasPointeeReadEffect =
                hasPointeeReadEffect || mayReadMemory;
            if (mayWriteMemory) {
                pointerCandidates.push_back(clone->clone());
            }
            argumentTerms_[term.get()] = clonePointer;
            if (argumentObservation_ == ArgumentObservation::ALL ||
                (argumentObservation_ == ArgumentObservation::VARIADIC_TAIL &&
                 argumentIndex >= prototype->parameters().size()))
            {
                observedArgumentTerms_.insert(clonePointer);
            }
            addArgumentRead(std::move(clone));
            ++argumentIndex;
        }

        /* A known variadic call still needs a fresh observation of its
         * non-fixed arguments on every semantic pass. The tail reads above
         * remain real call effects, but SignatureAnalyzer can distinguish
         * them from unrelated uses through observedArgumentTerms_. */
        if (argumentObservation_ != ArgumentObservation::NONE) {
            auto snapshotStatement =
                std::make_unique<RememberReachingDefinitions>();
            snapshotStatement_ = snapshotStatement.get();
            statements.push_back(std::move(snapshotStatement));
        }

        /*
         * Keep a pre-effect snapshot separate from the snapshot used for
         * signature inference below. Calls may read stack objects through any
         * pointer-valued argument, including parameters which are not marked
         * as writable by the prototype.
         */
        if (hasPointeeReadEffect) {
            auto pointeeReadSnapshot =
                std::make_unique<RememberReachingDefinitions>();
            pointeeReadSnapshotStatement_ = pointeeReadSnapshot.get();
            statements.push_back(std::move(pointeeReadSnapshot));
        }

        /*
         * This statement follows all argument reads so invalidating a local
         * buffer cannot erase another argument before its value is captured.
         */
        if (!completePrototype) {
            statements.push_back(std::make_unique<TrackedMemoryInvalidation>(
                TrackedMemoryInvalidation::ALL_TRACKED_MEMORY));
        } else if (!pointerCandidates.empty()) {
            statements.push_back(std::make_unique<TrackedMemoryInvalidation>(
                std::move(pointerCandidates)));
        }

        /* Argument values and pointee candidates have been captured. Kill
         * every ABI caller-saved register before defining the return value. */
        addCallClobbers();

        if (signatureIsInferred) {
            /* An inferred return is evidence, not an authoritative effect.
             * Recreate every ABI candidate so later uses can re-prove (or
             * replace) it on each pass. Keep the old term as a mapped write
             * for consumers during this pass, and mark it speculative only
             * when it still belongs to the active convention. */
            foreach (const auto &memoryLocation,
                     convention->returnValueLocations()) {
                auto term =
                    std::make_unique<MemoryLocationAccess>(memoryLocation);
                speculativeReturnValueTerms_.push_back(
                    std::make_pair(memoryLocation, term.get()));
                addReturnValueWrite(std::move(term));
            }

            if (signature->returnValue()) {
                auto clone = signature->returnValue()->clone();
                const Term *clonePointer = clone.get();
                returnValueTerms_[signature->returnValue().get()] =
                    clonePointer;
                if (const auto access =
                        signature->returnValue()->asMemoryLocationAccess())
                {
                    const MemoryLocation &location = access->memoryLocation();
                    if (convention->getReturnValueLocationCovering(location)) {
                        speculativeReturnValueTerms_.push_back(
                            std::make_pair(location, clonePointer));
                    }
                }
                addReturnValueWrite(std::move(clone));
            }
        } else if (signature->returnValue()) {
            auto clone = signature->returnValue()->clone();
            returnValueTerms_[signature->returnValue().get()] = clone.get();
            addReturnValueWrite(std::move(clone));
        }
    } else {
        argumentObservation_ = ArgumentObservation::ALL;
        auto snapshotStatement = std::make_unique<RememberReachingDefinitions>();
        snapshotStatement_ = snapshotStatement.get();
        statements.push_back(std::move(snapshotStatement));

        /* Signature inference consumes the pre-call snapshot. Until it has
         * produced a complete contract, any tracked caller-memory location may
         * also be observed or changed through a hidden or escaped pointer. */
        statements.push_back(std::make_unique<TrackedMemoryInvalidation>(
            TrackedMemoryInvalidation::ALL_TRACKED_MEMORY));

        addCallClobbers();

        foreach (const auto &memoryLocation, convention->returnValueLocations()) {
            auto term = std::make_unique<MemoryLocationAccess>(memoryLocation);
            speculativeReturnValueTerms_.push_back(std::make_pair(memoryLocation, term.get()));
            addReturnValueWrite(std::move(term));
        }
    }

    if (unknownStackCleanup) {
        if (convention->stackPointer()) {
            statements.push_back(std::make_unique<Assignment>(
                std::make_unique<MemoryLocationAccess>(convention->stackPointer()),
                std::make_unique<Intrinsic>(
                    Intrinsic::UNDEFINED,
                    convention->stackPointer().size<SmallBitSize>())));
        }
    } else if (stackCleanupSize && *stackCleanupSize != 0) {
        assert(convention->stackPointer());

        statements.push_back(std::make_unique<Assignment>(
            std::make_unique<MemoryLocationAccess>(convention->stackPointer()),
            std::make_unique<BinaryOperator>(
                BinaryOperator::ADD,
                std::make_unique<MemoryLocationAccess>(convention->stackPointer()),
                std::make_unique<Constant>(SizedValue(convention->stackPointer().size(), *stackCleanupSize)),
                convention->stackPointer().size<SmallBitSize>())));
    }
}

CallHook::~CallHook() {}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et ts=4 sw=4: */
