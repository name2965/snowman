/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "Signatures.h"

#include <cassert>
#include <utility>

#include <nc/common/Range.h>
#include <nc/core/ir/Terms.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

bool equivalentPrototypes(
        const std::shared_ptr<const FunctionPrototype> &left,
        const std::shared_ptr<const FunctionPrototype> &right) {
    if (left == right) {
        return true;
    }
    if (!left || !right) {
        return false;
    }
    return areFunctionPrototypesEquivalent(*left, *right);
}

bool equivalentTerms(const Term *left, const Term *right) {
    if (left == right) {
        return true;
    }
    if (!left || !right || left->kind() != right->kind() ||
        left->size() != right->size())
    {
        return false;
    }

    switch (left->kind()) {
    case Term::INT_CONST:
        return left->asConstant()->value().value() ==
            right->asConstant()->value().value();

    case Term::INTRINSIC:
        return left->asIntrinsic()->intrinsicKind() ==
            right->asIntrinsic()->intrinsicKind();

    case Term::MEMORY_LOCATION_ACCESS:
        return left->asMemoryLocationAccess()->memoryLocation() ==
            right->asMemoryLocationAccess()->memoryLocation();

    case Term::DEREFERENCE:
        return left->asDereference()->domain() ==
                right->asDereference()->domain() &&
            equivalentTerms(left->asDereference()->address(),
                            right->asDereference()->address());

    case Term::UNARY_OPERATOR:
        return left->asUnaryOperator()->operatorKind() ==
                right->asUnaryOperator()->operatorKind() &&
            equivalentTerms(left->asUnaryOperator()->operand(),
                            right->asUnaryOperator()->operand());

    case Term::BINARY_OPERATOR:
        return left->asBinaryOperator()->operatorKind() ==
                right->asBinaryOperator()->operatorKind() &&
            equivalentTerms(left->asBinaryOperator()->left(),
                            right->asBinaryOperator()->left()) &&
            equivalentTerms(left->asBinaryOperator()->right(),
                            right->asBinaryOperator()->right());
    }
    return false;
}

template<class Signature>
bool equivalentTermVectors(
        const std::vector<std::shared_ptr<const Term>> &left,
        const std::vector<std::shared_ptr<const Term>> &right,
        const Signature *) {
    if (left.size() != right.size()) {
        return false;
    }
    for (std::size_t index = 0; index < left.size(); ++index) {
        if (!equivalentTerms(left[index].get(), right[index].get())) {
            return false;
        }
    }
    return true;
}

bool equivalentSignatures(const FunctionSignature *left,
                          const FunctionSignature *right) {
    if (left == right) {
        return true;
    }
    return left && right && left->variadic() == right->variadic() &&
        equivalentTermVectors(left->arguments(), right->arguments(), left) &&
        equivalentTerms(left->returnValue().get(),
                        right->returnValue().get()) &&
        equivalentPrototypes(left->prototype(), right->prototype());
}

bool equivalentSignatures(const CallSignature *left,
                          const CallSignature *right) {
    if (left == right) {
        return true;
    }
    return left && right &&
        left->argumentEvidence() == right->argumentEvidence() &&
        equivalentTermVectors(left->arguments(), right->arguments(), left) &&
        equivalentTerms(left->returnValue().get(),
                        right->returnValue().get()) &&
        equivalentPrototypes(left->prototype(), right->prototype());
}

template<class Map>
bool equivalentMaps(const Map &left, const Map &right) {
    if (left.size() != right.size()) {
        return false;
    }
    for (const auto &entry : left) {
        const auto position = right.find(entry.first);
        if (position == right.end() ||
            !equivalentSignatures(entry.second.get(), position->second.get()))
        {
            return false;
        }
    }
    return true;
}

template<class Map>
const Map &externalReadView(bool updateInProgress,
                            const Map &committedSnapshot,
                            const Map &stagingSnapshot) {
    /* An external update replaces a complete snapshot. Readers must keep
     * observing the snapshot under which the current analysis products were
     * built, rather than a prefix of the snapshot being produced now. */
    return updateInProgress ? committedSnapshot : stagingSnapshot;
}

template<class Map, class Key, class Signature>
bool setBinding(Map &bindings, const Map *previousBindings,
                const Map &otherBindings, const Key &key,
                std::shared_ptr<Signature> signature,
                bool deferRevision, std::uint64_t &revision) {
    const Map &baseline = previousBindings ? *previousBindings : bindings;
    const auto oldPosition = baseline.find(key);
    const std::shared_ptr<Signature> oldSignature =
        oldPosition == baseline.end() ? std::shared_ptr<Signature>() :
                                        oldPosition->second;
    const bool changed = !equivalentSignatures(
        oldSignature.get(), signature.get());

    if (!signature) {
        bindings.erase(key);
    } else {
        /* Preserve stable identities for hook caches whenever semantics did
         * not change. The opposite provenance layer is also safe to reuse:
         * signature objects are completed before they are inserted. */
        if (oldSignature && equivalentSignatures(
                oldSignature.get(), signature.get()))
        {
            signature = oldSignature;
        } else {
            const auto currentPosition = bindings.find(key);
            if (currentPosition != bindings.end() &&
                equivalentSignatures(
                    currentPosition->second.get(), signature.get()))
            {
                signature = currentPosition->second;
            } else {
                const auto otherPosition = otherBindings.find(key);
                if (otherPosition != otherBindings.end() &&
                    equivalentSignatures(
                        otherPosition->second.get(), signature.get()))
                {
                    signature = otherPosition->second;
                }
            }
        }
        bindings[key] = std::move(signature);
    }

    if (changed && !deferRevision) {
        ++revision;
    }
    return changed;
}

} // anonymous namespace

Signatures::Signatures():
    inferenceUpdateInProgress_(false), externalUpdateInProgress_(false),
    revision_(0)
{}

void Signatures::beginInferenceUpdate() {
    assert(!inferenceUpdateInProgress_);
    assert(!externalUpdateInProgress_);
    previousAddressSignatures_ = inferredAddressSignatures_;
    previousFunctionSignatures_ = inferredFunctionSignatures_;
    previousCallSignatures_ = inferredCallSignatures_;
    inferredAddressSignatures_.clear();
    inferredFunctionSignatures_.clear();
    inferredCallSignatures_.clear();
    inferenceUpdateInProgress_ = true;
}

void Signatures::finishInferenceUpdate() {
    assert(inferenceUpdateInProgress_);
    const bool changed =
        !equivalentMaps(previousAddressSignatures_,
                        inferredAddressSignatures_) ||
        !equivalentMaps(previousFunctionSignatures_,
                        inferredFunctionSignatures_) ||
        !equivalentMaps(previousCallSignatures_, inferredCallSignatures_);
    previousAddressSignatures_.clear();
    previousFunctionSignatures_.clear();
    previousCallSignatures_.clear();
    inferenceUpdateInProgress_ = false;
    if (changed) {
        ++revision_;
    }
}

void Signatures::cancelInferenceUpdate() {
    assert(inferenceUpdateInProgress_);
    inferredAddressSignatures_.swap(previousAddressSignatures_);
    inferredFunctionSignatures_.swap(previousFunctionSignatures_);
    inferredCallSignatures_.swap(previousCallSignatures_);
    previousAddressSignatures_.clear();
    previousFunctionSignatures_.clear();
    previousCallSignatures_.clear();
    inferenceUpdateInProgress_ = false;
}

void Signatures::beginExternalUpdate() {
    assert(!externalUpdateInProgress_);
    assert(!inferenceUpdateInProgress_);
    previousExternalAddressSignatures_ = externalAddressSignatures_;
    previousExternalFunctionSignatures_ = externalFunctionSignatures_;
    previousExternalCallSignatures_ = externalCallSignatures_;
    externalAddressSignatures_.clear();
    externalFunctionSignatures_.clear();
    externalCallSignatures_.clear();
    externalUpdateInProgress_ = true;
}

void Signatures::finishExternalUpdate() {
    assert(externalUpdateInProgress_);
    const bool changed =
        !equivalentMaps(previousExternalAddressSignatures_,
                        externalAddressSignatures_) ||
        !equivalentMaps(previousExternalFunctionSignatures_,
                        externalFunctionSignatures_) ||
        !equivalentMaps(previousExternalCallSignatures_,
                        externalCallSignatures_);
    previousExternalAddressSignatures_.clear();
    previousExternalFunctionSignatures_.clear();
    previousExternalCallSignatures_.clear();
    externalUpdateInProgress_ = false;
    if (changed) {
        ++revision_;
    }
}

void Signatures::cancelExternalUpdate() {
    assert(externalUpdateInProgress_);
    externalAddressSignatures_.swap(previousExternalAddressSignatures_);
    externalFunctionSignatures_.swap(previousExternalFunctionSignatures_);
    externalCallSignatures_.swap(previousExternalCallSignatures_);
    previousExternalAddressSignatures_.clear();
    previousExternalFunctionSignatures_.clear();
    previousExternalCallSignatures_.clear();
    externalUpdateInProgress_ = false;
}

const std::shared_ptr<FunctionSignature> &Signatures::getSignature(
        ByteAddr addr) const {
    const auto &external = nc::find(
        externalReadView(
            externalUpdateInProgress_, previousExternalAddressSignatures_,
            externalAddressSignatures_),
        addr);
    return external ? external : nc::find(inferredAddressSignatures_, addr);
}

const std::shared_ptr<FunctionSignature> &Signatures::getSignature(
        ByteAddr addr, SignatureSource source) const {
    if (source == SignatureSource::EXTERNAL) {
        return nc::find(
            externalReadView(
                externalUpdateInProgress_,
                previousExternalAddressSignatures_,
                externalAddressSignatures_),
            addr);
    }
    return nc::find(inferredAddressSignatures_, addr);
}

bool Signatures::setSignature(
        ByteAddr addr, std::shared_ptr<FunctionSignature> signature,
        SignatureSource source) {
    if (source == SignatureSource::EXTERNAL) {
        return setBinding(
            externalAddressSignatures_,
            externalUpdateInProgress_ ?
                &previousExternalAddressSignatures_ : nullptr,
            inferredAddressSignatures_, addr, std::move(signature),
            externalUpdateInProgress_, revision_);
    }
    return setBinding(
        inferredAddressSignatures_,
        inferenceUpdateInProgress_ ? &previousAddressSignatures_ : nullptr,
        externalAddressSignatures_, addr, std::move(signature),
        inferenceUpdateInProgress_, revision_);
}

const std::shared_ptr<FunctionSignature> &Signatures::getSignature(
        const Function *function) const {
    assert(function != nullptr);
    const auto &external = nc::find(
        externalReadView(
            externalUpdateInProgress_, previousExternalFunctionSignatures_,
            externalFunctionSignatures_),
        function);
    return external ? external :
        nc::find(inferredFunctionSignatures_, function);
}

const std::shared_ptr<FunctionSignature> &Signatures::getSignature(
        const Function *function, SignatureSource source) const {
    assert(function != nullptr);
    if (source == SignatureSource::EXTERNAL) {
        return nc::find(
            externalReadView(
                externalUpdateInProgress_,
                previousExternalFunctionSignatures_,
                externalFunctionSignatures_),
            function);
    }
    return nc::find(inferredFunctionSignatures_, function);
}

bool Signatures::setSignature(
        const Function *function,
        std::shared_ptr<FunctionSignature> signature,
        SignatureSource source) {
    assert(function != nullptr);
    if (source == SignatureSource::EXTERNAL) {
        return setBinding(
            externalFunctionSignatures_,
            externalUpdateInProgress_ ?
                &previousExternalFunctionSignatures_ : nullptr,
            inferredFunctionSignatures_, function, std::move(signature),
            externalUpdateInProgress_, revision_);
    }
    return setBinding(
        inferredFunctionSignatures_,
        inferenceUpdateInProgress_ ? &previousFunctionSignatures_ : nullptr,
        externalFunctionSignatures_, function, std::move(signature),
        inferenceUpdateInProgress_, revision_);
}

const std::shared_ptr<CallSignature> &Signatures::getSignature(
        const Call *call) const {
    assert(call != nullptr);
    const auto &external = nc::find(
        externalReadView(
            externalUpdateInProgress_, previousExternalCallSignatures_,
            externalCallSignatures_),
        call);
    return external ? external : nc::find(inferredCallSignatures_, call);
}

const std::shared_ptr<CallSignature> &Signatures::getSignature(
        const Call *call, SignatureSource source) const {
    assert(call != nullptr);
    if (source == SignatureSource::EXTERNAL) {
        return nc::find(
            externalReadView(
                externalUpdateInProgress_, previousExternalCallSignatures_,
                externalCallSignatures_),
            call);
    }
    return nc::find(inferredCallSignatures_, call);
}

bool Signatures::setSignature(
        const Call *call, std::shared_ptr<CallSignature> signature,
        SignatureSource source) {
    assert(call != nullptr);
    if (source == SignatureSource::EXTERNAL) {
        return setBinding(
            externalCallSignatures_,
            externalUpdateInProgress_ ?
                &previousExternalCallSignatures_ : nullptr,
            inferredCallSignatures_, call, std::move(signature),
            externalUpdateInProgress_, revision_);
    }
    return setBinding(
        inferredCallSignatures_,
        inferenceUpdateInProgress_ ? &previousCallSignatures_ : nullptr,
        externalCallSignatures_, call, std::move(signature),
        inferenceUpdateInProgress_, revision_);
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
