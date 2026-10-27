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

#include <cstddef>
#include <memory>

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/Range.h>

#include <nc/core/ir/MemoryLocation.h>
#include <nc/core/ir/Term.h>

#include "DataflowStatus.h"
#include "ReachingDefinitions.h"

namespace nc {
namespace core {
namespace ir {
namespace dflow {

class Value;

/**
 * This class contains results of dataflow and constant propagation and folding analysis.
 */
class Dataflow {
    /** Mapping from a term to a description of its value. */
    boost::unordered_map<const Term *, std::unique_ptr<Value>> term2value_;

    /** Mapping from a term to its memory location. */
    boost::unordered_map<const Term *, MemoryLocation> term2location_;

    /**
     * Terms whose effective address resolved to more than one location while
     * iterating to a dataflow fixpoint.  Such a term is typically an indexed
     * loop access (for example, buffer[i]) and must not be treated as a read
     * from whichever concrete element happened to be visited last.
     */
    boost::unordered_set<const Term *> ambiguousLocations_;

    /** Monotonic counter for changes to the memory-location lattice. */
    std::size_t memoryLocationRevision_;

    /** Monotonic counter for changes to abstract values and provenance. */
    std::size_t valueRevision_;

    /** Lifecycle state of the abstract-interpretation result. */
    DataflowStatus analysisStatus_;

    /** Mapping from a term to the reaching definitions. */
    boost::unordered_map<const Term *, ReachingDefinitions> term2definitions_;

    /** Mapping from a statement to the reaching definitions. */
    boost::unordered_map<const Statement *, ReachingDefinitions> statement2definitions_;

public:
    /**
     * Constructor.
     */
    Dataflow();

    /**
     * Destructor.
     */
    ~Dataflow();

    /**
     * \param[in] term Valid pointer to a term.
     *
     * \return Pointer to the value description for this term. Can be nullptr.
     *         If the term is being assigned to, the value description
     *         for the right hand side of the assignment is returned.
     */
    Value *getValue(const Term *term);

    /**
     * \param[in] term Valid pointer to a term.
     *
     * \return Pointer to the value description for this term, or nullptr if
     *         the term was not evaluated by the analyzer.
     *         If the term is being assigned to, the value description
     *         for the right hand side of the assignment is returned.
     *
     * This overload never creates a lattice element or changes analysis
     * status. New code should prefer findValue() to make that explicit.
     */
    const Value *getValue(const Term *term) const;

    /**
     * Read-only lookup which never creates a lattice element and therefore
     * never invalidates a completed fixpoint.  Semantic transforms should
     * use this method when absence of a fact means "cannot prove".
     */
    const Value *findValue(const Term *term) const;

    /**
     * \return Mapping from a term to the description of its value.
     */
    boost::unordered_map<const Term *, std::unique_ptr<Value>> &term2value() { return term2value_; }

    /**
     * \return Mapping from a term to the description of its value.
     */
    const boost::unordered_map<const Term *, std::unique_ptr<Value>> &term2value() const { return term2value_; }

    /**
     * \param[in] term Valid pointer to a term.
     *
     * \return Memory location occupied by the term. If no memory location is associated
     *         with this term, an invalid MemoryLocation object is returned.
     */
    const ir::MemoryLocation &getMemoryLocation(const Term *term) const {
        assert(term != nullptr);
        return nc::find(term2location_, term);
    }

    /**
     * Associates a memory location with given term.
     *
     * \param[in] term Valid pointer to a term.
     * \param[in] memoryLocation Memory location.
     *
     * \return Const reference to the memory location stored in the object.
     */
    const MemoryLocation &setMemoryLocation(const Term *term, const MemoryLocation &memoryLocation) {
        assert(term != nullptr);

        auto &stored = term2location_[term];
        if (ambiguousLocations_.find(term) != ambiguousLocations_.end()) {
            stored = MemoryLocation();
            return stored;
        }

        /*
         * An unresolved location may become known as predecessor information
         * arrives.  Once a concrete location has been observed, however, a
         * different location (or an unresolved one) proves that this single
         * syntactic access denotes multiple runtime addresses.
         */
        if (stored && stored != memoryLocation) {
            ambiguousLocations_.insert(term);
            stored = MemoryLocation();
            ++memoryLocationRevision_;
            invalidateAnalysis();
        } else if (memoryLocation) {
            if (stored != memoryLocation) {
                stored = memoryLocation;
                ++memoryLocationRevision_;
                invalidateAnalysis();
            }
        }
        return stored;
    }

    /**
     * \return True if the term resolved to multiple effective addresses
     *         during fixpoint iteration.
     */
    bool hasAmbiguousMemoryLocation(const Term *term) const {
        assert(term != nullptr);
        return ambiguousLocations_.find(term) != ambiguousLocations_.end();
    }

    /**
     * Removes all location state for a term which is no longer in the IR.
     */
    void eraseMemoryLocation(const Term *term) {
        assert(term != nullptr);
        /* Do not combine these erases with ||.  Both containers can contain
         * the same term after a location becomes ambiguous, and short-circuit
         * evaluation would leave a stale pointer in ambiguousLocations_. */
        const bool hadLocation = term2location_.erase(term) != 0;
        const bool hadAmbiguity = ambiguousLocations_.erase(term) != 0;
        const bool changed = hadLocation || hadAmbiguity;
        if (changed) {
            ++memoryLocationRevision_;
            invalidateAnalysis();
        }
    }

    /**
     * A revision changes on UNKNOWN -> UNIQUE and UNIQUE -> AMBIGUOUS.
     * DataflowAnalyzer includes it in its fixpoint criterion so that a late
     * loss of address precision is propagated through earlier CFG blocks.
     */
    std::size_t memoryLocationRevision() const {
        return memoryLocationRevision_;
    }

    /**
     * A revision changes whenever an abstract value or one of its provenance
     * classifications changes.  It participates in fixpoint detection.
     */
    std::size_t valueRevision() const { return valueRevision_; }

    /**
     * \return True only when the analysis which produced these facts reached
     *         its fixpoint.  Transformations must not consume partial facts.
     */
    bool converged() const {
        return analysisStatus_ == DataflowStatus::CONVERGED;
    }

    /** Returns true while the analyzer is producing provisional facts. */
    bool running() const {
        return analysisStatus_ == DataflowStatus::RUNNING;
    }

    /** Returns true when the last analysis stopped without a fixpoint. */
    bool incomplete() const {
        return analysisStatus_ == DataflowStatus::INCOMPLETE;
    }

    /** Returns the lifecycle state of the abstract-interpretation result. */
    DataflowStatus analysisStatus() const { return analysisStatus_; }

    /** Changes the lifecycle state of the abstract-interpretation result. */
    void setAnalysisStatus(DataflowStatus status) { analysisStatus_ = status; }

    /**
     * Backwards-compatible completion setter. False denotes an analysis result
     * which is no longer running but did not reach a fixpoint.
     */
    void setConverged(bool converged) {
        analysisStatus_ = converged ?
            DataflowStatus::CONVERGED : DataflowStatus::INCOMPLETE;
    }

    /**
     * Invalidates a completed result while preserving the RUNNING state used
     * by instrumentation callbacks during fixpoint iteration.
     */
    void invalidateAnalysis() {
        if (analysisStatus_ == DataflowStatus::CONVERGED) {
            analysisStatus_ = DataflowStatus::INCOMPLETE;
        }
    }

    /** Drops facts belonging to IR statements removed after analysis. */
    void discardDetachedFacts();

    /**
     * \return Mapping from a term to its memory location.
     */
    boost::unordered_map<const Term *, MemoryLocation> &term2location() { return term2location_; };

    /**
     * \return Mapping from a term to its memory location.
     */
    const boost::unordered_map<const Term *, MemoryLocation> &term2location() const { return term2location_; };

    /**
     * \param[in] term Valid pointer to a read term.
     *
     * \return List of term's definitions. If not set before, it is empty.
     */
    ReachingDefinitions &getDefinitions(const Term *term) {
        assert(term != nullptr);
        assert(term->isRead());
        return term2definitions_[term];
    }

    /**
     * \param[in] term Valid pointer to a read term.
     *
     * \return List of term's definitions. If not set before, it is empty.
     */
    const ReachingDefinitions &getDefinitions(const Term *term) const {
        assert(term != nullptr);
        assert(term->isRead());
        return nc::find(term2definitions_, term);
    }

    /**
     * \return Mapping from a term to its reaching definitions.
     */
    boost::unordered_map<const Term *, ReachingDefinitions> &term2definitions() { return term2definitions_; }

    /**
     * \return Mapping from a term to its reaching definitions.
     */
    const boost::unordered_map<const Term *, ReachingDefinitions> &term2definitions() const { return term2definitions_; }

    /**
     * \param[in] statement Valid pointer to a read statement.
     *
     * \return Definitions reaching the given statement.
     */
    ReachingDefinitions &getDefinitions(const Statement *statement) {
        assert(statement != nullptr);
        return statement2definitions_[statement];
    }

    /**
     * \param[in] statement Valid pointer to a read statement.
     *
     * \return Definitions reaching the given statement.
     */
    const ReachingDefinitions &getDefinitions(const Statement *statement) const {
        assert(statement != nullptr);
        return nc::find(statement2definitions_, statement);
    }
};

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
