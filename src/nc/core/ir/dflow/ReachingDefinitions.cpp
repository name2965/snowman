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

#include "ReachingDefinitions.h"

#include <algorithm>
#include <iterator>

#include <QTextStream>

#include <nc/common/Foreach.h>

#include <nc/core/ir/Term.h>

namespace nc {
namespace core {
namespace ir {
namespace dflow {

bool ReachingDefinitions::hasUnknownDomainDefinition(
        Domain domain) const {
    if (domain >= MemoryDomain::FIRST_REGISTER &&
        domain <= MemoryDomain::LAST_REGISTER)
    {
        return hasUnknownRegisterDefinition_;
    }
    if (domain == MemoryDomain::STACK) {
        return hasUnknownStackDefinition_;
    }
    return hasUnknownOtherMemoryDefinition_;
}

bool ReachingDefinitions::hasIncomingDomainDefinition(
        Domain domain) const {
    if (domain >= MemoryDomain::FIRST_REGISTER &&
        domain <= MemoryDomain::LAST_REGISTER)
    {
        return hasIncomingRegisterDefinition_;
    }
    if (domain == MemoryDomain::STACK) {
        return hasIncomingStackDefinition_;
    }
    return hasIncomingOtherMemoryDefinition_;
}

void ReachingDefinitions::addUnknownDomainDefinitions(
        bool includeRegisters, bool includeStack,
        bool includeOtherMemory) {
    if (!includeRegisters && !includeStack && !includeOtherMemory) {
        return;
    }

    foreach (Chunk &chunk, chunks_) {
        const Domain domain = chunk.location().domain();
        const bool isRegister =
            domain >= MemoryDomain::FIRST_REGISTER &&
            domain <= MemoryDomain::LAST_REGISTER;
        if ((includeRegisters && isRegister) ||
            (includeStack && domain == MemoryDomain::STACK) ||
            (includeOtherMemory && !isRegister &&
             domain != MemoryDomain::STACK))
        {
            chunk.addUnknownDefinition();
        }
    }

    /* These are may-writes, not definite kills.  Before the first wildcard
     * in a domain, every unrepresented interval denotes its function-entry
     * value. Preserve that implicit alternative for intervals which are first
     * observed later. Without this promotion, an extent-less call/asm write
     * would incorrectly turn such a read into unknown-only. */
    if (includeRegisters && !hasUnknownRegisterDefinition_) {
        hasIncomingRegisterDefinition_ = true;
    }
    if (includeStack && !hasUnknownStackDefinition_) {
        hasIncomingStackDefinition_ = true;
    }
    if (includeOtherMemory && !hasUnknownOtherMemoryDefinition_) {
        hasIncomingOtherMemoryDefinition_ = true;
    }

    hasUnknownRegisterDefinition_ =
        hasUnknownRegisterDefinition_ || includeRegisters;
    hasUnknownStackDefinition_ =
        hasUnknownStackDefinition_ || includeStack;
    hasUnknownOtherMemoryDefinition_ =
        hasUnknownOtherMemoryDefinition_ || includeOtherMemory;
    selfTest();
}

void ReachingDefinitions::addDefinition(const MemoryLocation &mloc, const Term *term) {
    assert(mloc);

    killDefinitions(mloc);
    
    auto i = std::lower_bound(chunks_.begin(), chunks_.end(), mloc,
        [](const Chunk &a, const MemoryLocation &b) -> bool {
            return a.location() < b;
        });

    chunks_.insert(i, Chunk(mloc, std::vector<const Term *>(1, term)));

    selfTest();
}

void ReachingDefinitions::addUnknownDefinition(const MemoryLocation &mloc) {
    assert(mloc);

    killDefinitions(mloc);

    auto i = std::lower_bound(chunks_.begin(), chunks_.end(), mloc,
        [](const Chunk &a, const MemoryLocation &b) -> bool {
            return a.location() < b;
        });

    chunks_.insert(i, Chunk(mloc, std::vector<const Term *>(), true));

    selfTest();
}

void ReachingDefinitions::killDefinitions(const MemoryLocation &mloc) {
    assert(mloc);

    if (chunks_.empty()) {
        return;
    }

    std::vector<Chunk> result;
    result.reserve(chunks_.size() + 1);

    foreach (auto &chunk, chunks_) {
        if (!mloc.overlaps(chunk.location())) {
            result.push_back(std::move(chunk));
        } else {
            if (chunk.location().addr() < mloc.addr()) {
                if (mloc.endAddr() < chunk.location().endAddr()) {
                    result.push_back(Chunk(
                        MemoryLocation(mloc.domain(), chunk.location().addr(), mloc.addr() - chunk.location().addr()),
                        chunk.definitions(), chunk.hasUnknownDefinition(),
                        chunk.hasIncomingDefinition()));
                } else {
                    result.push_back(Chunk(
                        MemoryLocation(mloc.domain(), chunk.location().addr(), mloc.addr() - chunk.location().addr()),
                        std::move(chunk.definitions()), chunk.hasUnknownDefinition(),
                        chunk.hasIncomingDefinition()));
                }
            }
            if (mloc.endAddr() < chunk.location().endAddr()) {
                result.push_back(Chunk(
                    MemoryLocation(mloc.domain(), mloc.endAddr(), chunk.location().endAddr() - mloc.endAddr()),
                    std::move(chunk.definitions()), chunk.hasUnknownDefinition(),
                    chunk.hasIncomingDefinition()));
            }
        }
    }

    chunks_ = std::move(result);

    selfTest();
}

void ReachingDefinitions::project(const MemoryLocation &mloc, ReachingDefinitions &result) const {
    assert(mloc);

    result.clear();

    const bool hasDomainUnknown =
        hasUnknownDomainDefinition(mloc.domain());
    const bool hasDomainIncoming =
        hasIncomingDomainDefinition(mloc.domain());
    BitAddr coveredUntil = mloc.addr();

    foreach (const auto &chunk, chunks_) {
        if (chunk.location().domain() == mloc.domain()) {
            auto addr = std::max(chunk.location().addr(), mloc.addr());
            auto endAddr = std::min(chunk.location().endAddr(), mloc.endAddr());

            if (addr < endAddr) {
                if (hasDomainUnknown && coveredUntil < addr) {
                    result.chunks_.push_back(Chunk(
                        MemoryLocation(
                            mloc.domain(), coveredUntil,
                            addr - coveredUntil),
                        std::vector<const Term *>(), true,
                        hasDomainIncoming));
                }
                result.chunks_.push_back(Chunk(
                    MemoryLocation(mloc.domain(), addr, endAddr - addr),
                    chunk.definitions(),
                    chunk.hasUnknownDefinition() ||
                        (hasDomainUnknown &&
                         chunk.definitions().empty()),
                    chunk.hasIncomingDefinition() ||
                        (hasDomainIncoming &&
                         chunk.definitions().empty())));
                coveredUntil = endAddr;
            }
        }
    }

    if (hasDomainUnknown && coveredUntil < mloc.endAddr()) {
        result.chunks_.push_back(Chunk(
            MemoryLocation(
                mloc.domain(), coveredUntil,
                mloc.endAddr() - coveredUntil),
            std::vector<const Term *>(), true,
            hasDomainIncoming));
    }

    result.selfTest();
}

std::vector<MemoryLocation> ReachingDefinitions::getDefinedMemoryLocationsWithin(Domain domain) const {
    std::vector<MemoryLocation> result;
    result.reserve(chunks_.size());

    foreach (const auto &chunk, chunks_) {
        if (chunk.location().domain() == domain) {
            result.push_back(chunk.location());
        }
    }

    return result;
}

void ReachingDefinitions::merge(const ReachingDefinitions &those) {
    mergeImpl(those, false);
}

void ReachingDefinitions::joinAlternative(
        const ReachingDefinitions &those) {
    mergeImpl(those, true);
}

void ReachingDefinitions::mergeImpl(
        const ReachingDefinitions &those, bool alternative) {
    selfTest();
    those.selfTest();

    std::vector<Chunk> result;
    result.reserve(chunks_.size() + those.chunks_.size());

    auto i = chunks_.begin();
    auto iend = chunks_.end();

    auto j = those.chunks_.begin();
    auto jend = those.chunks_.end();

    auto unknownFromThis = [this](Domain domain) {
        return hasUnknownDomainDefinition(domain);
    };
    auto unknownFromThose = [&those](Domain domain) {
        return those.hasUnknownDomainDefinition(domain);
    };
    auto incomingFromThis = [this, alternative](Domain domain) {
        return hasIncomingDomainDefinition(domain) ||
            (alternative && !hasUnknownDomainDefinition(domain));
    };
    auto incomingFromThose = [&those, alternative](Domain domain) {
        return those.hasIncomingDomainDefinition(domain) ||
            (alternative && !those.hasUnknownDomainDefinition(domain));
    };
    auto effectiveUnknownFromThis =
        [this](const Chunk &chunk, Domain domain) {
            return chunk.hasUnknownDefinition() ||
                (chunk.definitions().empty() &&
                 hasUnknownDomainDefinition(domain));
        };
    auto effectiveUnknownFromThose =
        [&those](const Chunk &chunk, Domain domain) {
            return chunk.hasUnknownDefinition() ||
                (chunk.definitions().empty() &&
                 those.hasUnknownDomainDefinition(domain));
        };
    auto effectiveIncomingFromThis =
        [this](const Chunk &chunk, Domain domain) {
            return chunk.hasIncomingDefinition() ||
                (chunk.definitions().empty() &&
                 hasIncomingDomainDefinition(domain));
        };
    auto effectiveIncomingFromThose =
        [&those](const Chunk &chunk, Domain domain) {
            return chunk.hasIncomingDefinition() ||
                (chunk.definitions().empty() &&
                 those.hasIncomingDomainDefinition(domain));
        };

    while (i != iend || j != jend) {
        auto a = i != iend ? i->location() : MemoryLocation();
        auto b = j != jend ? j->location() : MemoryLocation();

        if (!result.empty()) {
            const auto &c = result.back().location();
            if (c.domain() == a.domain() && c.endAddr() > a.addr()) {
                a = MemoryLocation(a.domain(), c.endAddr(), a.endAddr() - c.endAddr());
            }
            if (c.domain() == b.domain() && c.endAddr() > b.addr()) {
                b = MemoryLocation(b.domain(), c.endAddr(), b.endAddr() - c.endAddr());
            }
        }

        if (!b) {
            result.push_back(Chunk(
                a, i->definitions(),
                effectiveUnknownFromThis(*i, a.domain()) ||
                    unknownFromThose(a.domain()),
                effectiveIncomingFromThis(*i, a.domain()) ||
                    incomingFromThose(a.domain())));
            ++i;
        } else if (!a) {
            result.push_back(Chunk(
                b, j->definitions(),
                effectiveUnknownFromThose(*j, b.domain()) ||
                    unknownFromThis(b.domain()),
                effectiveIncomingFromThose(*j, b.domain()) ||
                    incomingFromThis(b.domain())));
            ++j;
        } else if (a.domain() < b.domain()) {
            result.push_back(Chunk(
                a, i->definitions(),
                effectiveUnknownFromThis(*i, a.domain()) ||
                    unknownFromThose(a.domain()),
                effectiveIncomingFromThis(*i, a.domain()) ||
                    incomingFromThose(a.domain())));
            ++i;
        } else if (b.domain() < a.domain()) {
            result.push_back(Chunk(
                b, j->definitions(),
                effectiveUnknownFromThose(*j, b.domain()) ||
                    unknownFromThis(b.domain()),
                effectiveIncomingFromThose(*j, b.domain()) ||
                    incomingFromThis(b.domain())));
            ++j;
        } else if (a.endAddr() <= b.addr()) {
            result.push_back(Chunk(
                a, i->definitions(),
                effectiveUnknownFromThis(*i, a.domain()) ||
                    unknownFromThose(a.domain()),
                effectiveIncomingFromThis(*i, a.domain()) ||
                    incomingFromThose(a.domain())));
            ++i;
        } else if (b.endAddr() <= a.addr()) {
            result.push_back(Chunk(
                b, j->definitions(),
                effectiveUnknownFromThose(*j, b.domain()) ||
                    unknownFromThis(b.domain()),
                effectiveIncomingFromThose(*j, b.domain()) ||
                    incomingFromThis(b.domain())));
            ++j;
        } else if (a.addr() < b.addr()) {
            result.push_back(Chunk(MemoryLocation(a.domain(), a.addr(), b.addr() - a.addr()),
                                   i->definitions(),
                                   effectiveUnknownFromThis(
                                       *i, a.domain()) ||
                                       unknownFromThose(a.domain()),
                                   effectiveIncomingFromThis(
                                       *i, a.domain()) ||
                                       incomingFromThose(a.domain())));
        } else if (b.addr() < a.addr()) {
            result.push_back(Chunk(MemoryLocation(b.domain(), b.addr(), a.addr() - b.addr()),
                                   j->definitions(),
                                   effectiveUnknownFromThose(
                                       *j, b.domain()) ||
                                       unknownFromThis(b.domain()),
                                   effectiveIncomingFromThose(
                                       *j, b.domain()) ||
                                       incomingFromThis(b.domain())));
        } else {
            std::vector<const Term *> merged;
            merged.reserve(i->definitions().size() + j->definitions().size());
            std::set_union(i->definitions().begin(), i->definitions().end(), j->definitions().begin(), j->definitions().end(), std::back_inserter(merged));

            if (a.size() < b.size()) {
                result.push_back(Chunk(a, std::move(merged),
                    effectiveUnknownFromThis(*i, a.domain()) ||
                        effectiveUnknownFromThose(*j, a.domain()),
                    effectiveIncomingFromThis(*i, a.domain()) ||
                        effectiveIncomingFromThose(*j, a.domain())));
                ++i;
            } else if (b.size() < a.size()) {
                result.push_back(Chunk(b, std::move(merged),
                    effectiveUnknownFromThis(*i, b.domain()) ||
                        effectiveUnknownFromThose(*j, b.domain()),
                    effectiveIncomingFromThis(*i, b.domain()) ||
                        effectiveIncomingFromThose(*j, b.domain())));
                ++j;
            } else {
                result.push_back(Chunk(a, std::move(merged),
                    effectiveUnknownFromThis(*i, a.domain()) ||
                        effectiveUnknownFromThose(*j, a.domain()),
                    effectiveIncomingFromThis(*i, a.domain()) ||
                        effectiveIncomingFromThose(*j, a.domain())));
                ++i;
                ++j;
            }
        }
    }

    const bool registerUnknownWasDifferent =
        hasUnknownRegisterDefinition_ !=
        those.hasUnknownRegisterDefinition_;
    const bool stackUnknownWasDifferent =
        hasUnknownStackDefinition_ !=
        those.hasUnknownStackDefinition_;
    const bool otherMemoryUnknownWasDifferent =
        hasUnknownOtherMemoryDefinition_ !=
        those.hasUnknownOtherMemoryDefinition_;

    chunks_ = std::move(result);
    hasUnknownRegisterDefinition_ =
        hasUnknownRegisterDefinition_ ||
        those.hasUnknownRegisterDefinition_;
    hasUnknownStackDefinition_ =
        hasUnknownStackDefinition_ ||
        those.hasUnknownStackDefinition_;
    hasUnknownOtherMemoryDefinition_ =
        hasUnknownOtherMemoryDefinition_ ||
        those.hasUnknownOtherMemoryDefinition_;
    hasIncomingRegisterDefinition_ =
        hasIncomingRegisterDefinition_ ||
        those.hasIncomingRegisterDefinition_ ||
        (alternative && registerUnknownWasDifferent);
    hasIncomingStackDefinition_ =
        hasIncomingStackDefinition_ ||
        those.hasIncomingStackDefinition_ ||
        (alternative && stackUnknownWasDifferent);
    hasIncomingOtherMemoryDefinition_ =
        hasIncomingOtherMemoryDefinition_ ||
        those.hasIncomingOtherMemoryDefinition_ ||
        (alternative && otherMemoryUnknownWasDifferent);

    selfTest();
}

void ReachingDefinitions::print(QTextStream &out) const {
    out << '{';
    if (hasUnknownRegisterDefinition_) {
        out << " register-domain:unknown;";
    }
    if (hasUnknownStackDefinition_) {
        out << " stack-domain:unknown;";
    }
    if (hasUnknownOtherMemoryDefinition_) {
        out << " memory-domain:unknown;";
    }
    if (hasIncomingRegisterDefinition_) {
        out << " register-domain:incoming;";
    }
    if (hasIncomingStackDefinition_) {
        out << " stack-domain:incoming;";
    }
    if (hasIncomingOtherMemoryDefinition_) {
        out << " memory-domain:incoming;";
    }
    foreach (const auto &chunk, chunks_) {
        out << chunk.location() << ':';
        if (chunk.hasUnknownDefinition()) {
            out << " unknown";
        }
        if (chunk.hasIncomingDefinition()) {
            out << " incoming";
        }
        foreach (const Term *term, chunk.definitions()) {
            out << ' ' << *term;
        }
        out << ';';
    }
    out << '}';
}

} // namespace dflow
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
