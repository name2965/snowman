/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

/* * SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
 * Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
 * Alexander Fokin, Sergey Levin, Leonid Tsvetkov
 *
 * This file is part of SmartDec decompiler.
 *
 * SmartDec decompiler is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SmartDec decompiler is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include <nc/config.h>

#include <algorithm>
#include <cassert>
#include <vector>

#include <nc/common/Foreach.h>
#include <nc/common/Printable.h>

#include <nc/core/ir/MemoryLocation.h>

namespace nc {
namespace core {
namespace ir {

class Term;

namespace dflow {

/**
 * Reaching definitions.
 */
class ReachingDefinitions: public PrintableBase<ReachingDefinitions> {
public:
    /*
     * Memory location and the list of terms defining this memory location.
     */
    class Chunk {
        MemoryLocation location_; ///< Memory location.
        std::vector<const Term *> definitions_; ///< Terms defining this memory location.
        bool hasUnknownDefinition_; ///< Whether an unmodelled write may define this location.
        bool hasIncomingDefinition_; ///< Whether the function-entry value may reach this location.

        public:

        /*
         * Constructor.
         *
         * \param location               Valid memory location.
         * \param definitions            Terms defining this location.
         * \param hasUnknownDefinition   Whether a value-less write reaches it.
         * \param hasIncomingDefinition  Whether its entry value reaches it.
         */
        Chunk(const MemoryLocation &location, std::vector<const Term *> definitions,
              bool hasUnknownDefinition = false,
              bool hasIncomingDefinition = false):
            location_(location), definitions_(std::move(definitions)),
            hasUnknownDefinition_(hasUnknownDefinition),
            hasIncomingDefinition_(hasIncomingDefinition)
        {
            assert(location);
        }

        /**
         * \return Memory location.
         */
        const MemoryLocation &location() const { return location_; }

        /**
         * \return List of terms defining the memory location.
         */
        std::vector<const Term *> &definitions() { return definitions_; }

        /**
         * \return List of terms defining the memory location.
         */
        const std::vector<const Term *> &definitions() const { return definitions_; }

        /**
         * \return True when this location can also be defined by an operation
         *         whose value has no corresponding IR term.
         */
        bool hasUnknownDefinition() const { return hasUnknownDefinition_; }

        /**
         * \return True when a control-flow alternative reaches this location
         *         without a definition produced inside the function.
         *
         * This is distinct from hasUnknownDefinition(): an incoming value is
         * the value present at function entry, whereas an unknown definition
         * denotes an explicitly modelled but value-less write.
         */
        bool hasIncomingDefinition() const {
            return hasIncomingDefinition_;
        }

        /** Adds a value-less may-definition to this exact interval. */
        void addUnknownDefinition() { hasUnknownDefinition_ = true; }

        /**
         * \param that Another object of the same type.
         *
         * \return True if *this and that have the same memory location and list of terms,
         *         false otherwise.
         */
        bool operator==(const Chunk &that) const {
            return location_ == that.location_ && definitions_ == that.definitions_ &&
                   hasUnknownDefinition_ == that.hasUnknownDefinition_ &&
                   hasIncomingDefinition_ == that.hasIncomingDefinition_;
        }
    };

private:
    /**
     * Pairs of memory locations and terms defining them.
     * The pairs are sorted by memory location.
     * Terms are sorted using default comparator.
     */
    std::vector<Chunk> chunks_;

    /*
     * An extent-less write (for example through an escaped pointer) also
     * applies to intervals which have not been observed yet.  Existing
     * chunks receive an explicit unknown marker immediately; these category
     * markers cover future gaps.  A later exact definition creates a chunk
     * without the marker and therefore shadows earlier extent-less writes for
     * precisely that range while leaving the rest of the domain conservative.
     */
    bool hasUnknownRegisterDefinition_ = false;
    bool hasUnknownStackDefinition_ = false;
    bool hasUnknownOtherMemoryDefinition_ = false;
    bool hasIncomingRegisterDefinition_ = false;
    bool hasIncomingStackDefinition_ = false;
    bool hasIncomingOtherMemoryDefinition_ = false;

public:
    /**
     * \return Pairs of memory locations and vectors of terms defining them.
     *         The pairs are sorted by memory location.
     *         Terms are sorted using default comparator.
     */
    const std::vector<Chunk> &chunks() const { return chunks_; }

    /**
     * \return True if the list of pairs (chunks) is empty, false otherwise.
     */
    bool empty() const {
        return chunks_.empty() &&
            !hasUnknownRegisterDefinition_ &&
            !hasUnknownStackDefinition_ &&
            !hasUnknownOtherMemoryDefinition_ &&
            !hasIncomingRegisterDefinition_ &&
            !hasIncomingStackDefinition_ &&
            !hasIncomingOtherMemoryDefinition_;
    }

    /**
     * Clears the reaching definitions.
     */
    void clear() {
        chunks_.clear();
        hasUnknownRegisterDefinition_ = false;
        hasUnknownStackDefinition_ = false;
        hasUnknownOtherMemoryDefinition_ = false;
        hasIncomingRegisterDefinition_ = false;
        hasIncomingStackDefinition_ = false;
        hasIncomingOtherMemoryDefinition_ = false;
    }

    /**
     * Adds an extent-less unknown may-definition for selected domain classes.
     * The marker survives until exact later definitions shadow individual
     * ranges, including ranges which are first observed after this call.
     */
    void addUnknownDomainDefinitions(
        bool includeRegisters, bool includeStack, bool includeOtherMemory);

    /**
     * Adds a definition of memory location, removing all previous definitions of overlapping memory locations.
     *
     * \param[in] memoryLocation Memory location.
     * \param[in] term Term which is the definition.
     */
    void addDefinition(const MemoryLocation &memoryLocation, const Term *term);

    /**
     * Replaces definitions of a location with an unknown definition.
     *
     * Unlike merely killing definitions, retaining an explicit unknown keeps
     * constant propagation sound when this state is merged with a path on
     * which an older concrete definition still reaches the join.
     */
    void addUnknownDefinition(const MemoryLocation &memoryLocation);

    /**
     * Kills definitions of given memory location.
     *
     * \param[in] memoryLocation Memory location.
     */
    void killDefinitions(const MemoryLocation &memoryLocation);

    /**
     * Computes a subset of reaching definitions defining (parts of)
     * given memory location.
     *
     * \param[in]  memoryLocation   Memory location.
     * \param[out] result           Resulting reaching definitions.
     */
    void project(const MemoryLocation &memoryLocation, ReachingDefinitions &result) const;

    /**
     * \param[in]  memoryLocation   Memory location.
     *
     * \return A subset of reaching definitions defining (parts of)
     * given memory location.
     *
     * \note Prefer using project() as it does less memory allocations.
     */
    ReachingDefinitions projected(const MemoryLocation &memoryLocation) const {
        ReachingDefinitions result;
        project(memoryLocation, result);
        return result;
    }

    /**
     * \return All defined memory locations in the domain.
     *
     * \param[in] domain Domain.
     */
    std::vector<MemoryLocation> getDefinedMemoryLocationsWithin(Domain domain) const;

    /**
     * Adds given reaching definitions to the list of known reaching definitions.
     *
     * \param[in] those Reaching definitions.
     */
    void merge(const ReachingDefinitions &those);

    /**
     * Joins definitions from another mutually exclusive control-flow path.
     *
     * In contrast with merge(), a bit range represented on only one side is
     * marked as also having an incoming definition.  This records that the
     * other path preserves the value which existed before any definition in
     * the current function.  Overlapping and partially overlapping chunks
     * are split so the marker applies only to the one-sided subranges.
     *
     * \param[in] those Reaching definitions from another CFG alternative.
     */
    void joinAlternative(const ReachingDefinitions &those);

    /**
     * \return True, if these and given reaching definitions are the same.
     *
     * \param[in] those Reaching definitions.
     */
    bool operator==(const ReachingDefinitions &those) const {
        return chunks_ == those.chunks_ &&
            hasUnknownRegisterDefinition_ ==
                those.hasUnknownRegisterDefinition_ &&
            hasUnknownStackDefinition_ ==
                those.hasUnknownStackDefinition_ &&
            hasUnknownOtherMemoryDefinition_ ==
                those.hasUnknownOtherMemoryDefinition_ &&
            hasIncomingRegisterDefinition_ ==
                those.hasIncomingRegisterDefinition_ &&
            hasIncomingStackDefinition_ ==
                those.hasIncomingStackDefinition_ &&
            hasIncomingOtherMemoryDefinition_ ==
                those.hasIncomingOtherMemoryDefinition_;
    }

    /**
     * \return True, if these and given reaching definitions are different.
     *
     * \param[in] those Reaching definitions.
     */
    bool operator!=(const ReachingDefinitions &those) const { return !(*this == those); }

    /**
     * Removes all reaching definitions for which given predicate returns true.
     *
     * \param pred Predicate functor accepting two arguments: a memory location
     *             and a valid pointer to a term covering this location.
     * \tparam T Predicate functor type.
     */
    template<class T>
    void filterOut(const T &pred) {
        selfTest();
        foreach (auto &chunk, chunks_) {
            chunk.definitions().erase(
                std::remove_if(chunk.definitions().begin(), chunk.definitions().end(),
                    [&](const Term *term) -> bool { return pred(chunk.location(), term); }),
                chunk.definitions().end());
        }
        chunks_.erase(
            std::remove_if(chunks_.begin(), chunks_.end(),
                [](const Chunk &chunk) -> bool {
                    return chunk.definitions().empty() &&
                        !chunk.hasUnknownDefinition() &&
                        !chunk.hasIncomingDefinition();
                }),
            chunks_.end());
        selfTest();
    }

    void print(QTextStream &out) const;

private:
    /**
     * Checks if the data structure is in a valid state.
     * Fails with an assertion if not.
     */
    void selfTest() const {
#ifndef NDEBUG
        assert(!hasIncomingRegisterDefinition_ ||
               hasUnknownRegisterDefinition_);
        assert(!hasIncomingStackDefinition_ ||
               hasUnknownStackDefinition_);
        assert(!hasIncomingOtherMemoryDefinition_ ||
               hasUnknownOtherMemoryDefinition_);
        for (std::size_t i = 1; i < chunks_.size(); ++i) {
            assert(chunks_[i-1].location() < chunks_[i].location());
            if (chunks_[i-1].location().domain() ==
                chunks_[i].location().domain())
            {
                assert(chunks_[i-1].location().endAddr() <=
                       chunks_[i].location().addr());
            }
        }
#endif
    }

    /** Combines another definition set, optionally treating it as a mutually
     * exclusive CFG alternative rather than a may-write overlay. */
    void mergeImpl(const ReachingDefinitions &those, bool alternative);

    /** Whether a future unrepresented interval in this domain is unknown. */
    bool hasUnknownDomainDefinition(Domain domain) const;

    /** Whether an entry value is a default alternative in this domain. */
    bool hasIncomingDomainDefinition(Domain domain) const;
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
