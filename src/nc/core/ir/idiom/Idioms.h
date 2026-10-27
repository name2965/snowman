/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cassert>
#include <memory>

#include <boost/unordered_map.hpp>

#include "MemoryFill.h"

namespace nc {
namespace core {
namespace ir {

class Function;

namespace idiom {

/** Semantic idioms recovered for one function. */
class FunctionIdioms {
    boost::unordered_map<const BasicBlock *,
        std::unique_ptr<const MemoryFill>> memoryFills_;
    boost::unordered_map<const cflow::Region *,
        const MemoryFill *> regionMemoryFills_;

public:
    /** Adds a proven memory fill. There may be at most one per loop header. */
    void addMemoryFill(std::unique_ptr<MemoryFill> memoryFill) {
        assert(memoryFill != nullptr);
        const BasicBlock *loopHeader = memoryFill->loopHeader();
        assert(memoryFills_.find(loopHeader) == memoryFills_.end());

        if (const cflow::Region *region = memoryFill->region()) {
            assert(regionMemoryFills_.find(region) == regionMemoryFills_.end());
            regionMemoryFills_.emplace(region, memoryFill.get());
        }
        memoryFills_.emplace(loopHeader, std::move(memoryFill));
    }

    /** Returns the memory fill implemented by a natural-loop header. */
    const MemoryFill *getMemoryFill(const BasicBlock *loopHeader) const {
        assert(loopHeader != nullptr);
        auto i = memoryFills_.find(loopHeader);
        return i == memoryFills_.end() ? nullptr : i->second.get();
    }

    /** Returns the memory fill mapped to a structured region, or nullptr. */
    const MemoryFill *getMemoryFill(const cflow::Region *region) const {
        assert(region != nullptr);
        auto i = regionMemoryFills_.find(region);
        return i == regionMemoryFills_.end() ? nullptr : i->second;
    }

    const boost::unordered_map<const BasicBlock *,
        std::unique_ptr<const MemoryFill>> &memoryFills() const {
        return memoryFills_;
    }
};

/** Mapping from functions to their recovered semantic idioms. */
class Idioms: public boost::unordered_map<
    const Function *, std::unique_ptr<const FunctionIdioms>> {};

} // namespace idiom
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
