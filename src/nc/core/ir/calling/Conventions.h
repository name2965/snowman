/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cassert>

#include <boost/optional.hpp>
#include <boost/unordered_map.hpp>

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
    /** Mapping from a callee id to the associated calling convention. */
    boost::unordered_map<CalleeId, const Convention *> id2convention_;

    /** Mapping from a callee id to the size of its arguments passed on the stack. */
    boost::unordered_map<CalleeId, ByteSize> id2stackArgumentsSize_;

    /**
     * Mapping from a callee id to a stack adjustment proved from return
     * instructions.  This is deliberately independent of argument placement:
     * RET N proves an execution effect, not a source-level ABI.
     */
    boost::unordered_map<CalleeId, ReturnStackCleanup> id2returnStackCleanup_;

public:

    /**
     * Assigns a calling convention to a callee id.
     *
     * \param calleeId Callee id.
     * \param convention Pointer to a calling convention of the function. Can be nullptr.
     */
    void setConvention(const CalleeId &calleeId, const Convention *convention) {
        id2convention_[calleeId] = convention;
    }

    /**
     * \param calleeId Callee id.
     *
     * \return Pointer to the calling convention used for calls to given address. Can be nullptr.
     */
    const Convention *getConvention(const CalleeId &calleeId) const {
        return nc::find(id2convention_, calleeId);
    }

    /**
     * Sets the stack arguments size for the given callee id.
     *
     * \param calleeId Callee id.
     * \param size Size of the arguments passed on the stack, or boost::none if unknown.
     */
    void setStackArgumentsSize(const CalleeId &calleeId, const boost::optional<ByteSize> &size) {
        if (size) {
            id2stackArgumentsSize_[calleeId] = *size;
        } else {
            id2stackArgumentsSize_.erase(calleeId);
        }
    }

    /**
     * \param calleeId Callee id.
     *
     * \return Size of the arguments passed on the stack, or boost::none if unknown.
     */
    boost::optional<ByteSize> getStackArgumentsSize(const CalleeId &calleeId) const {
        return nc::find_optional(id2stackArgumentsSize_, calleeId);
    }

    /**
     * Records the stack adjustment performed by the callee on return.
     *
     * This fact can override a convention's default cleanup behavior without
     * changing that convention's register and stack argument locations.
     */
    void setReturnStackCleanupSize(const CalleeId &calleeId, ByteSize size) {
        id2returnStackCleanup_[calleeId] = ReturnStackCleanup::exact(size);
    }

    /**
     * Records that reachable return instructions have incompatible stack
     * adjustments, or that a return effect could not be represented.
     */
    void setConflictingReturnStackCleanup(const CalleeId &calleeId) {
        id2returnStackCleanup_[calleeId] = ReturnStackCleanup::conflicting();
    }

    /** Clears all return-instruction evidence for a callee. */
    void clearReturnStackCleanup(const CalleeId &calleeId) {
        id2returnStackCleanup_.erase(calleeId);
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
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
