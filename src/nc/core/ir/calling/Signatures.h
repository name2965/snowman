/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cstdint>
#include <memory>

#include <boost/unordered_map.hpp>

#include <nc/common/Types.h>

#include "CallSignature.h"
#include "FunctionSignature.h"

namespace nc {
namespace core {
namespace ir {

class Call;
class Function;

namespace calling {

/** Origin of a signature binding. */
enum class SignatureSource {
    /** Contract reconstructed from program observations. */
    INFERRED,

    /** Contract supplied by trusted external metadata. */
    EXTERNAL
};

/**
 * Signatures of functions and calls to functions.
 *
 * Inferred and external contracts are deliberately retained in separate
 * layers. Consumers see an external contract when one exists, while an
 * analysis pass can still update the inferred layer underneath it. This is
 * required for contracts with an authoritative fixed prefix and inferred
 * call-site details, such as the tail of a variadic argument list.
 */
class Signatures {
    typedef boost::unordered_map<ByteAddr,
        std::shared_ptr<FunctionSignature>> AddressSignatures;
    typedef boost::unordered_map<const Function *,
        std::shared_ptr<FunctionSignature>> FunctionSignatures;
    typedef boost::unordered_map<const Call *,
        std::shared_ptr<CallSignature>> CallSignatures;

    AddressSignatures inferredAddressSignatures_;
    FunctionSignatures inferredFunctionSignatures_;
    CallSignatures inferredCallSignatures_;

    AddressSignatures externalAddressSignatures_;
    FunctionSignatures externalFunctionSignatures_;
    CallSignatures externalCallSignatures_;

    /* Snapshot used to replace, rather than accumulate, one inference pass. */
    AddressSignatures previousAddressSignatures_;
    FunctionSignatures previousFunctionSignatures_;
    CallSignatures previousCallSignatures_;
    bool inferenceUpdateInProgress_;

    AddressSignatures previousExternalAddressSignatures_;
    FunctionSignatures previousExternalFunctionSignatures_;
    CallSignatures previousExternalCallSignatures_;
    bool externalUpdateInProgress_;

    std::uint64_t revision_;

public:
    Signatures();

    /**
     * Monotonically increasing semantic revision of both provenance layers.
     * Structurally equivalent replacements do not advance the revision.
     */
    std::uint64_t revision() const { return revision_; }

    /**
     * Starts replacement of the complete inferred layer.
     *
     * Every inferred signature produced before finishInferenceUpdate() is
     * part of the new snapshot. Entries not reproduced by the analysis are
     * removed. External bindings are unaffected.
     */
    void beginInferenceUpdate();

    /** Commits the inferred snapshot and advances revision() if it changed. */
    void finishInferenceUpdate();

    /** Discards a partial inferred snapshot after an analysis failure. */
    void cancelInferenceUpdate();

    /**
     * Starts replacement of the complete external metadata layer.
     *
     * Until finishExternalUpdate(), every getter observes the previously
     * committed external snapshot. New bindings are write-only staging data;
     * a producer that needs a fact it just staged must retain that fact in
     * its local record instead of reading it back through this registry.
     */
    void beginExternalUpdate();

    /** Commits the external snapshot and advances revision() if it changed. */
    void finishExternalUpdate();

    /** Discards a partial external snapshot after a metadata failure. */
    void cancelExternalUpdate();

    /** Returns the effective (external-first) signature at an address. */
    const std::shared_ptr<FunctionSignature> &getSignature(ByteAddr addr) const;

    /** Returns the signature from exactly one provenance layer. */
    const std::shared_ptr<FunctionSignature> &getSignature(
        ByteAddr addr, SignatureSource source) const;

    /**
     * Sets one provenance layer. A null signature removes that binding.
     *
     * \return True if the semantic contents of the layer changed.
     */
    bool setSignature(ByteAddr addr,
                      std::shared_ptr<FunctionSignature> signature,
                      SignatureSource source = SignatureSource::INFERRED);

    /** Returns the effective (external-first) signature of a function. */
    const std::shared_ptr<FunctionSignature> &getSignature(
        const Function *function) const;

    /** Returns the function signature from exactly one provenance layer. */
    const std::shared_ptr<FunctionSignature> &getSignature(
        const Function *function, SignatureSource source) const;

    /** Sets one provenance layer for a function. */
    bool setSignature(const Function *function,
                      std::shared_ptr<FunctionSignature> signature,
                      SignatureSource source = SignatureSource::INFERRED);

    /** Returns the effective (external-first) signature of a call. */
    const std::shared_ptr<CallSignature> &getSignature(
        const Call *call) const;

    /** Returns the call signature from exactly one provenance layer. */
    const std::shared_ptr<CallSignature> &getSignature(
        const Call *call, SignatureSource source) const;

    /** Sets one provenance layer for a call. */
    bool setSignature(const Call *call,
                      std::shared_ptr<CallSignature> signature,
                      SignatureSource source = SignatureSource::INFERRED);
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
