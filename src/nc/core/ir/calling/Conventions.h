/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cassert>
#include <cstdint>
#include <utility>

#include <boost/optional.hpp>
#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/Range.h>

#include "CalleeId.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

class Convention;

/**
 * Stack-pointer effect observed at a function's return instructions.
 *
 * Absence of evidence is intentionally different from conflicting evidence:
 * the former permits an ABI default, while the latter means that a single
 * post-call stack-pointer value cannot safely be synthesized.
 */
class ReturnStackCleanup {
public:
    enum Kind {
        UNKNOWN,
        EXACT,
        CONFLICTING
    };

private:
    Kind kind_;
    ByteSize size_;

    ReturnStackCleanup(Kind kind, ByteSize size):
        kind_(kind), size_(size)
    {}

public:
    ReturnStackCleanup(): kind_(UNKNOWN), size_(0) {}

    static ReturnStackCleanup exact(ByteSize size) {
        assert(size >= 0);
        return ReturnStackCleanup(EXACT, size);
    }

    static ReturnStackCleanup conflicting() {
        return ReturnStackCleanup(CONFLICTING, 0);
    }

    Kind kind() const { return kind_; }
    bool isUnknown() const { return kind_ == UNKNOWN; }
    bool isExact() const { return kind_ == EXACT; }
    bool isConflicting() const { return kind_ == CONFLICTING; }

    ByteSize size() const {
        assert(isExact());
        return size_;
    }
};

/**
 * Information about assigned calling conventions and their parameters.
 */
class Conventions {
    typedef boost::unordered_map<CalleeId, const Convention *>
        ConventionMap;
    typedef boost::unordered_map<CalleeId, ByteSize> StackArgumentsSizeMap;
    typedef boost::unordered_map<CalleeId, boost::optional<ByteSize>>
        ExternalStackArgumentsSizeMap;

    /** Mapping from a callee id to the associated calling convention. */
    ConventionMap id2convention_;

    /**
     * Convention entries installed only as target-specific defaults while a
     * callee is unresolved.  A fallback on a CallAddress must not override a
     * convention learned later from the resolved target or authoritative
     * symbol metadata.
     */
    boost::unordered_set<CalleeId> fallbackConventions_;

    /** Mapping from a callee id to the size of its arguments passed on the stack. */
    StackArgumentsSizeMap id2stackArgumentsSize_;

    /** Authoritative metadata for the current external-analysis snapshot. */
    ConventionMap externalConventions_;
    ExternalStackArgumentsSizeMap externalStackArgumentsSizes_;

    /** Previous snapshot, retained until an external update is committed. */
    ConventionMap previousExternalConventions_;
    ExternalStackArgumentsSizeMap previousExternalStackArgumentsSizes_;
    bool externalUpdateInProgress_ = false;

    /** Monotonic revision of all convention facts visible to analysis. */
    std::uint64_t revision_ = 0;

    /**
     * Mapping from a callee id to a stack adjustment proved from return
     * instructions.  This is deliberately independent of argument placement:
     * RET N proves an execution effect, not a source-level ABI.
     */
    boost::unordered_map<CalleeId, ReturnStackCleanup> id2returnStackCleanup_;

    /**
     * Callees whose recovered Function is only an external forwarding stub.
     * Such a body establishes control flow, but supplies no implementation
     * reads from which formal arguments can be reconstructed.
     */
    boost::unordered_set<CalleeId> opaqueExternalBodies_;

    template<class Map>
    static bool mapsEqual(const Map &left, const Map &right) {
        if (left.size() != right.size()) {
            return false;
        }
        for (const auto &entry: left) {
            const auto position = right.find(entry.first);
            if (position == right.end() || position->second != entry.second) {
                return false;
            }
        }
        return true;
    }

    static bool returnStackCleanupEqual(
            const ReturnStackCleanup &left,
            const ReturnStackCleanup &right) {
        return left.kind() == right.kind() &&
            (!left.isExact() || left.size() == right.size());
    }

    const ConventionMap &externalConventionReadView() const {
        return externalUpdateInProgress_ ?
            previousExternalConventions_ : externalConventions_;
    }

    const ExternalStackArgumentsSizeMap &
            externalStackArgumentsSizeReadView() const {
        return externalUpdateInProgress_ ?
            previousExternalStackArgumentsSizes_ :
            externalStackArgumentsSizes_;
    }

public:

    /** Monotonic semantic revision of persistent and external facts. */
    std::uint64_t revision() const { return revision_; }

    /**
     * Starts replacement of the complete external convention snapshot.
     * Entries not reproduced before finishExternalUpdate() are removed.
     * All getters continue to observe the previously committed snapshot
     * until then. The new snapshot is write-only staging data, so producers
     * must use their local metadata records instead of reading staged facts
     * back through this object.
     */
    void beginExternalUpdate() {
        assert(!externalUpdateInProgress_);

        /* Copy into temporaries first, so allocation failure cannot leave a
         * half-started transaction or disturb the effective old snapshot. */
        ConventionMap oldConventions(externalConventions_);
        ExternalStackArgumentsSizeMap oldSizes(
            externalStackArgumentsSizes_);
        previousExternalConventions_.swap(oldConventions);
        previousExternalStackArgumentsSizes_.swap(oldSizes);
        externalConventions_.clear();
        externalStackArgumentsSizes_.clear();
        externalUpdateInProgress_ = true;
    }

    /** Commits a complete external snapshot. */
    void finishExternalUpdate() noexcept {
        assert(externalUpdateInProgress_);
        const bool changed =
            !mapsEqual(previousExternalConventions_,
                       externalConventions_) ||
            !mapsEqual(previousExternalStackArgumentsSizes_,
                       externalStackArgumentsSizes_);
        previousExternalConventions_.clear();
        previousExternalStackArgumentsSizes_.clear();
        externalUpdateInProgress_ = false;
        if (changed) {
            ++revision_;
        }
    }

    /** Rolls back a partial external snapshot. */
    void cancelExternalUpdate() noexcept {
        assert(externalUpdateInProgress_);
        externalConventions_.swap(previousExternalConventions_);
        externalStackArgumentsSizes_.swap(
            previousExternalStackArgumentsSizes_);
        previousExternalConventions_.clear();
        previousExternalStackArgumentsSizes_.clear();
        externalUpdateInProgress_ = false;
    }

    /**
     * Assigns a calling convention to a callee id.
     *
     * \param calleeId Callee id.
     * \param convention Pointer to a calling convention of the function. Can be nullptr.
     */
    void setConvention(const CalleeId &calleeId, const Convention *convention) {
        const auto position = id2convention_.find(calleeId);
        const bool wasFallback = fallbackConventions_.erase(calleeId) != 0;
        bool changed = wasFallback;

        if (convention) {
            if (position == id2convention_.end() ||
                position->second != convention)
            {
                id2convention_[calleeId] = convention;
                changed = true;
            }
        } else if (position != id2convention_.end()) {
            id2convention_.erase(position);
            changed = true;
        }

        if (changed) {
            ++revision_;
        }
    }

    /**
     * Installs a default convention without replacing stronger evidence.
     */
    void setFallbackConvention(
            const CalleeId &calleeId, const Convention *convention) {
        if (convention &&
            id2convention_.find(calleeId) == id2convention_.end())
        {
            const auto insertedConvention = id2convention_.insert(
                std::make_pair(calleeId, convention));
            assert(insertedConvention.second);
            try {
                fallbackConventions_.insert(calleeId);
            } catch (...) {
                /* Never let an allocation failure turn a default into an
                 * authoritative convention merely because its provenance
                 * marker could not be recorded. */
                id2convention_.erase(insertedConvention.first);
                throw;
            }
            ++revision_;
        }
    }

    /** Sets authoritative convention metadata for one external snapshot. */
    void setExternalConvention(
            const CalleeId &calleeId, const Convention *convention) {
        const ConventionMap &baseline = externalUpdateInProgress_ ?
            previousExternalConventions_ : externalConventions_;
        const auto oldPosition = baseline.find(calleeId);
        const bool changed = convention ?
            (oldPosition == baseline.end() ||
             oldPosition->second != convention) :
            oldPosition != baseline.end();

        if (convention) {
            externalConventions_[calleeId] = convention;
        } else {
            externalConventions_.erase(calleeId);
        }
        if (changed && !externalUpdateInProgress_) {
            ++revision_;
        }
    }

    /**
     * \param calleeId Callee id.
     *
     * \return Pointer to the calling convention used for calls to given address. Can be nullptr.
     */
    const Convention *getConvention(const CalleeId &calleeId) const {
        const Convention *external =
            nc::find(externalConventionReadView(), calleeId);
        return external ? external : nc::find(id2convention_, calleeId);
    }

    /** Returns only the persistent convention, ignoring external metadata. */
    const Convention *getPersistentConvention(
            const CalleeId &calleeId) const {
        return nc::find(id2convention_, calleeId);
    }

    /** Returns only convention metadata from the external layer. */
    const Convention *getExternalConvention(
            const CalleeId &calleeId) const {
        return nc::find(externalConventionReadView(), calleeId);
    }

    /** Whether the current convention is only an unresolved default. */
    bool isFallbackConvention(const CalleeId &calleeId) const {
        return !getExternalConvention(calleeId) &&
            fallbackConventions_.find(calleeId) !=
                fallbackConventions_.end();
    }

    /**
     * Sets the stack arguments size for the given callee id.
     *
     * \param calleeId Callee id.
     * \param size Size of the arguments passed on the stack, or boost::none if unknown.
     */
    void setStackArgumentsSize(const CalleeId &calleeId, const boost::optional<ByteSize> &size) {
        if (size) {
            const auto position = id2stackArgumentsSize_.find(calleeId);
            if (position == id2stackArgumentsSize_.end() ||
                position->second != *size)
            {
                id2stackArgumentsSize_[calleeId] = *size;
                ++revision_;
            }
        } else {
            if (id2stackArgumentsSize_.erase(calleeId) != 0) {
                ++revision_;
            }
        }
    }

    /**
     * Sets authoritative stack-size metadata for one external snapshot.
     * boost::none is a real external fact meaning that the fixed size is
     * unknown (for example at a variadic call); it masks persistent evidence.
     * Omitting the callee from a replacement snapshot removes the binding.
     */
    void setExternalStackArgumentsSize(
            const CalleeId &calleeId,
            const boost::optional<ByteSize> &size) {
        const ExternalStackArgumentsSizeMap &baseline =
            externalUpdateInProgress_ ?
            previousExternalStackArgumentsSizes_ :
            externalStackArgumentsSizes_;
        const auto oldPosition = baseline.find(calleeId);
        const bool changed = oldPosition == baseline.end() ||
            oldPosition->second != size;

        externalStackArgumentsSizes_[calleeId] = size;
        if (changed && !externalUpdateInProgress_) {
            ++revision_;
        }
    }

    /**
     * \param calleeId Callee id.
     *
     * \return Size of the arguments passed on the stack, or boost::none if unknown.
     */
    boost::optional<ByteSize> getStackArgumentsSize(const CalleeId &calleeId) const {
        const auto &externalSizes = externalStackArgumentsSizeReadView();
        const auto external = externalSizes.find(calleeId);
        return external != externalSizes.end() ?
            external->second :
            nc::find_optional(id2stackArgumentsSize_, calleeId);
    }

    /** Returns only the persistent stack argument size. */
    boost::optional<ByteSize> getPersistentStackArgumentsSize(
            const CalleeId &calleeId) const {
        return nc::find_optional(id2stackArgumentsSize_, calleeId);
    }

    /** Returns only stack-size metadata from the external layer. */
    boost::optional<ByteSize> getExternalStackArgumentsSize(
            const CalleeId &calleeId) const {
        const auto &externalSizes = externalStackArgumentsSizeReadView();
        const auto position = externalSizes.find(calleeId);
        return position == externalSizes.end() ?
            boost::optional<ByteSize>() : position->second;
    }

    /** Whether external metadata explicitly binds a size, including none. */
    bool hasExternalStackArgumentsSizeBinding(
            const CalleeId &calleeId) const {
        const auto &externalSizes = externalStackArgumentsSizeReadView();
        return externalSizes.find(calleeId) != externalSizes.end();
    }

    /**
     * Records the stack adjustment performed by the callee on return.
     *
     * This fact can override a convention's default cleanup behavior without
     * changing that convention's register and stack argument locations.
     */
    void setReturnStackCleanupSize(const CalleeId &calleeId, ByteSize size) {
        if (opaqueExternalBodies_.find(calleeId) !=
            opaqueExternalBodies_.end())
        {
            return;
        }
        const ReturnStackCleanup cleanup =
            ReturnStackCleanup::exact(size);
        const auto position = id2returnStackCleanup_.find(calleeId);
        if (position == id2returnStackCleanup_.end() ||
            !returnStackCleanupEqual(position->second, cleanup))
        {
            id2returnStackCleanup_[calleeId] = cleanup;
            ++revision_;
        }
    }

    /**
     * Records that reachable return instructions have incompatible stack
     * adjustments, or that a return effect could not be represented.
     */
    void setConflictingReturnStackCleanup(const CalleeId &calleeId) {
        if (opaqueExternalBodies_.find(calleeId) !=
            opaqueExternalBodies_.end())
        {
            return;
        }
        const ReturnStackCleanup cleanup =
            ReturnStackCleanup::conflicting();
        const auto position = id2returnStackCleanup_.find(calleeId);
        if (position == id2returnStackCleanup_.end() ||
            !returnStackCleanupEqual(position->second, cleanup))
        {
            id2returnStackCleanup_[calleeId] = cleanup;
            ++revision_;
        }
    }

    /** Clears all return-instruction evidence for a callee. */
    void clearReturnStackCleanup(const CalleeId &calleeId) {
        if (id2returnStackCleanup_.erase(calleeId) != 0) {
            ++revision_;
        }
    }

    /**
     * \return Return-instruction evidence. UNKNOWN means that no usable body
     * evidence was observed; EXACT includes an exact zero-byte adjustment.
     */
    ReturnStackCleanup getReturnStackCleanup(const CalleeId &calleeId) const {
        auto result = id2returnStackCleanup_.find(calleeId);
        return result == id2returnStackCleanup_.end() ?
            ReturnStackCleanup() : result->second;
    }

    /**
     * Marks whether a recovered function body is merely an opaque external
     * forwarding boundary (for example an import jump thunk).
     *
     * This is not prototype evidence and does not select a convention.  It
     * only prevents the empty forwarding body from suppressing independent
     * call-site evidence.
     */
    void setExternalBodyOpaque(const CalleeId &calleeId, bool opaque = true) {
        bool changed = false;
        if (opaque) {
            changed = opaqueExternalBodies_.insert(calleeId).second;
            /* Return cleanup is implementation-side evidence. A validated
             * forwarding boundary has no local return implementation, so a
             * previously analyzed tail jump must not survive as CONFLICTING
             * (nor as an accidental exact effect). */
            changed = id2returnStackCleanup_.erase(calleeId) != 0 ||
                changed;
        } else {
            changed = opaqueExternalBodies_.erase(calleeId) != 0;
        }
        if (changed) {
            ++revision_;
        }
    }

    /** Returns true iff the recovered body carries no callee ABI evidence. */
    bool isExternalBodyOpaque(const CalleeId &calleeId) const {
        return opaqueExternalBodies_.find(calleeId) !=
            opaqueExternalBodies_.end();
    }
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
