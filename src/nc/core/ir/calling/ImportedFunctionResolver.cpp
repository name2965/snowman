/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "ImportedFunctionResolver.h"

#include <climits>
#include <cstddef>
#include <limits>
#include <vector>

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <nc/common/Foreach.h>
#include <nc/core/image/Relocation.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/ReachingDefinitions.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

bool getImportSlotLocation(ByteAddr slot, SmallBitSize pointerSize,
                           MemoryLocation &result) {
    if (slot < 0 || pointerSize <= 0 || pointerSize % CHAR_BIT != 0) {
        return false;
    }

    const BitAddr maximumStart =
        (std::numeric_limits<BitAddr>::max)() - pointerSize;
    if (slot > maximumStart / CHAR_BIT) {
        return false;
    }
    result = MemoryLocation(
        MemoryDomain::MEMORY, slot * CHAR_BIT, pointerSize);
    return true;
}

bool mayOverwriteSlot(const Statement *statement,
                      const dflow::Dataflow &dataflow,
                      const MemoryLocation &slotLocation) {
    if (statement->is<InlineAssembly>()) {
        return true;
    }

    if (statement->is<TrackedMemoryInvalidation>()) {
        /* These statements are synthesized by CallHook from the very
         * prototype contracts being refined. They describe caller-owned
         * memory reachable through a call, not a decoded write to static
         * linkage storage. Treating their pointer candidates as IAT writes
         * creates non-monotone feedback: installing a prototype can make its
         * own import origin disappear on the next pass. Explicit decoded
         * writes and inline assembly below remain the evidence for linkage
         * patching in this static-image model. */
        return false;
    }

    const Term *written = nullptr;
    if (const Assignment *assignment = statement->asAssignment()) {
        written = assignment->left();
    } else if (const Touch *touch = statement->asTouch()) {
        if (touch->accessType() == Term::WRITE) {
            written = touch->term();
        }
    }
    if (!written) {
        return false;
    }

    MemoryLocation location = dataflow.getMemoryLocation(written);
    if (!location) {
        if (const MemoryLocationAccess *access =
                written->asMemoryLocationAccess())
        {
            location = access->memoryLocation();
        }
    }
    if (location) {
        return location.overlaps(slotLocation);
    }

    /* An unresolved image-memory write can alias any import slot. Other
     * abstract domains (registers and stack) cannot. */
    if (const Dereference *dereference = written->asDereference()) {
        return dereference->domain() == MemoryDomain::MEMORY;
    }
    return false;
}

bool blockMayOverwriteSlot(const BasicBlock *block,
                           const Statement *stopBefore,
                           const dflow::Dataflow &dataflow,
                           const MemoryLocation &slotLocation) {
    foreach (const Statement *statement, block->statements()) {
        if (statement == stopBefore) {
            return false;
        }
        if (mayOverwriteSlot(statement, dataflow, slotLocation)) {
            return true;
        }
    }
    /* A non-null cutoff not found in its alleged block is stale/foreign. */
    return stopBefore != nullptr;
}

class Resolver {
    const dflow::Dataflow &dataflow_;
    const ImportRelocationLookup &lookup_;
    SmallBitSize pointerSize_;
    std::size_t remainingTerms_;
    boost::unordered_set<const Term *> visiting_;
    boost::unordered_map<const Term *, const image::Symbol *> resolved_;
    boost::unordered_set<const Term *> failed_;

    static const std::size_t MAX_DEPTH = 64;
    static const std::size_t MAX_TERMS = 4096;

public:
    Resolver(const dflow::Dataflow &dataflow,
             const ImportRelocationLookup &lookup,
             SmallBitSize pointerSize):
        dataflow_(dataflow), lookup_(lookup), pointerSize_(pointerSize),
        remainingTerms_(MAX_TERMS)
    {}

    const image::Symbol *resolve(const Term *term) {
        return resolve(term, 0);
    }

private:
    const image::Symbol *resolve(const Term *term, std::size_t depth) {
        if (!term || term->size() != pointerSize_ ||
            depth > MAX_DEPTH || remainingTerms_ == 0)
        {
            return nullptr;
        }

        const auto resolved = resolved_.find(term);
        if (resolved != resolved_.end()) {
            return resolved->second;
        }
        if (failed_.find(term) != failed_.end() ||
            !visiting_.insert(term).second)
        {
            return nullptr;
        }
        --remainingTerms_;

        const image::Symbol *result = resolveUncached(term, depth);
        visiting_.erase(term);
        if (result) {
            resolved_[term] = result;
        } else {
            failed_.insert(term);
        }
        return result;
    }

    const image::Symbol *resolveUncached(
            const Term *term, std::size_t depth) {
        if (!term->statement()) {
            return nullptr;
        }

        if (term->isWrite()) {
            const Assignment *assignment =
                term->statement()->asAssignment();
            if (!assignment || assignment->left() != term ||
                !assignment->right())
            {
                return nullptr;
            }
            return resolve(assignment->right(), depth + 1);
        }

        if (const Dereference *dereference = term->asDereference()) {
            if (const image::Symbol *symbol =
                    resolveRelocationLoad(dereference))
            {
                return symbol;
            }
        }

        if (!term->isRead()) {
            return nullptr;
        }

        const MemoryLocation &location =
            dataflow_.getMemoryLocation(term);
        if (!location || location.size() != pointerSize_ ||
            dataflow_.hasAmbiguousMemoryLocation(term))
        {
            return nullptr;
        }

        const dflow::ReachingDefinitions &definitions =
            dataflow_.getDefinitions(term);
        if (definitions.chunks().size() != 1) {
            return nullptr;
        }

        const dflow::ReachingDefinitions::Chunk &chunk =
            definitions.chunks().front();
        if (chunk.location() != location ||
            chunk.hasUnknownDefinition() ||
            chunk.hasIncomingDefinition() ||
            chunk.definitions().empty())
        {
            return nullptr;
        }

        const image::Symbol *result = nullptr;
        for (const Term *definition : chunk.definitions()) {
            if (!definition ||
                dataflow_.getMemoryLocation(definition) != location)
            {
                return nullptr;
            }
            const image::Symbol *candidate =
                resolve(definition, depth + 1);
            if (!candidate || (result && result != candidate)) {
                return nullptr;
            }
            result = candidate;
        }
        return result;
    }

    const image::Symbol *resolveRelocationLoad(
            const Dereference *dereference) const {
        if (!dereference || dereference->domain() != MemoryDomain::MEMORY ||
            dereference->size() != pointerSize_ ||
            dataflow_.hasAmbiguousMemoryLocation(dereference))
        {
            return nullptr;
        }

        const MemoryLocation &location =
            dataflow_.getMemoryLocation(dereference);
        if (!location || location.domain() != MemoryDomain::MEMORY ||
            location.size() != pointerSize_ || location.addr() < 0 ||
            location.addr() % CHAR_BIT != 0)
        {
            return nullptr;
        }

        const ByteAddr slot = location.addr() / CHAR_BIT;
        const image::Relocation *relocation = lookup_(slot);
        const ByteSize pointerBytes = pointerSize_ / CHAR_BIT;
        if (!relocation || relocation->address() != slot ||
            relocation->size() != pointerBytes || relocation->addend() != 0)
        {
            return nullptr;
        }

        const image::Symbol *symbol = relocation->symbol();
        if (!symbol || symbol->type() != image::SymbolType::FUNCTION ||
            symbol->value())
        {
            return nullptr;
        }
        if (!isImportSlotUnmodifiedBefore(
                dereference->statement(), dataflow_, pointerSize_, slot))
        {
            return nullptr;
        }
        return symbol;
    }
};

} // anonymous namespace

bool isImportSlotUnmodifiedBefore(
        const Statement *statement, const dflow::Dataflow &dataflow,
        SmallBitSize pointerSize, ByteAddr slot) {
    if (!statement || !statement->basicBlock() || !dataflow.converged()) {
        return false;
    }

    MemoryLocation slotLocation;
    if (!getImportSlotLocation(slot, pointerSize, slotLocation)) {
        return false;
    }

    const BasicBlock *cutoffBlock = statement->basicBlock();
    const Function *function = cutoffBlock->function();
    if (!function) {
        return false;
    }

    const CFG cfg(function->basicBlocks());
    boost::unordered_set<const BasicBlock *> precedingBlocks;
    const auto &cutoffPredecessors = cfg.getPredecessors(cutoffBlock);
    std::vector<const BasicBlock *> worklist(
        cutoffPredecessors.begin(), cutoffPredecessors.end());
    bool cutoffBlockCanRepeat = false;

    while (!worklist.empty()) {
        const BasicBlock *block = worklist.back();
        worklist.pop_back();
        if (block == cutoffBlock) {
            cutoffBlockCanRepeat = true;
            continue;
        }
        if (!precedingBlocks.insert(block).second) {
            continue;
        }
        const auto &predecessors = cfg.getPredecessors(block);
        worklist.insert(
            worklist.end(), predecessors.begin(), predecessors.end());
    }

    foreach (const BasicBlock *block, precedingBlocks) {
        if (blockMayOverwriteSlot(
                block, nullptr, dataflow, slotLocation))
        {
            return false;
        }
    }

    /* Without a back edge, statements after the load/call cannot affect this
     * execution. With a cycle they precede a possible later execution and
     * therefore must be checked too. */
    const Statement *stopBefore = cutoffBlockCanRepeat ? nullptr : statement;
    return !blockMayOverwriteSlot(
        cutoffBlock, stopBefore, dataflow, slotLocation);
}

bool mayFunctionOverwriteImportSlot(
        const Function *function, const dflow::Dataflow &dataflow,
        SmallBitSize pointerSize, ByteAddr slot) {
    if (!function || !dataflow.converged()) {
        return true;
    }

    MemoryLocation slotLocation;
    if (!getImportSlotLocation(slot, pointerSize, slotLocation)) {
        return true;
    }

    foreach (const BasicBlock *block, function->basicBlocks()) {
        if (blockMayOverwriteSlot(block, nullptr, dataflow, slotLocation)) {
            return true;
        }
    }
    return false;
}

const image::Symbol *resolveImportedFunction(
        const Call *call, const dflow::Dataflow &dataflow,
        SmallBitSize pointerSize, const ImportRelocationLookup &lookup) {
    if (!call || !dataflow.converged() || pointerSize <= 0 ||
        pointerSize % CHAR_BIT != 0 || !lookup)
    {
        return nullptr;
    }

    return Resolver(dataflow, lookup, pointerSize).resolve(call->target());
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
