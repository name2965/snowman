/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "SymbolPrototypeRegistry.h"

#include <functional>
#include <set>
#include <tuple>
#include <utility>

#include "FunctionPrototype.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

typedef std::pair<const FunctionPrototype *, const FunctionPrototype *>
    PrototypePair;

struct PrototypePairLess {
    bool operator()(const PrototypePair &left,
                    const PrototypePair &right) const {
        std::less<const FunctionPrototype *> less;
        if (less(left.first, right.first)) {
            return true;
        }
        if (less(right.first, left.first)) {
            return false;
        }
        return less(left.second, right.second);
    }
};

bool equivalentPrototypes(const FunctionPrototype &left,
                          const FunctionPrototype &right,
                          std::set<PrototypePair, PrototypePairLess> &visited) {
    if (&left == &right) {
        return true;
    }

    const PrototypePair pair(&left, &right);
    if (!visited.insert(pair).second) {
        return true;
    }

    if (left.returnType() != right.returnType() ||
        left.callingConvention() != right.callingConvention() ||
        left.preferredName() != right.preferredName() ||
        left.memoryEffectsAreComplete() !=
            right.memoryEffectsAreComplete() ||
        left.parameters().size() != right.parameters().size())
    {
        return false;
    }

    for (std::size_t index = 0; index < left.parameters().size(); ++index) {
        const ParameterDescription &leftParameter = left.parameters()[index];
        const ParameterDescription &rightParameter = right.parameters()[index];
        if (leftParameter.name() != rightParameter.name() ||
            leftParameter.type() != rightParameter.type() ||
            leftParameter.pointeeAccess() !=
                rightParameter.pointeeAccess())
        {
            return false;
        }

        const std::shared_ptr<const FunctionPrototype> &leftCallback =
            leftParameter.callbackPrototype();
        const std::shared_ptr<const FunctionPrototype> &rightCallback =
            rightParameter.callbackPrototype();
        if (static_cast<bool>(leftCallback) !=
            static_cast<bool>(rightCallback))
        {
            return false;
        }
        if (leftCallback && !equivalentPrototypes(
                *leftCallback, *rightCallback, visited))
        {
            return false;
        }
    }

    return true;
}

bool equivalentRecords(const SymbolPrototypeRecord &left,
                       const SymbolPrototypeRecord &right) {
    if (!left.prototype() || !right.prototype() ||
        left.conventionName() != right.conventionName() ||
        left.doesNotReturn() != right.doesNotReturn() ||
        static_cast<bool>(left.stackArgumentsSize()) !=
            static_cast<bool>(right.stackArgumentsSize()))
    {
        return false;
    }
    if (left.stackArgumentsSize() &&
        *left.stackArgumentsSize() != *right.stackArgumentsSize())
    {
        return false;
    }

    std::set<PrototypePair, PrototypePairLess> visited;
    return equivalentPrototypes(
        *left.prototype(), *right.prototype(), visited);
}

} // anonymous namespace

SymbolPrototypeRegistry::AddResult SymbolPrototypeRegistry::add(
        QString canonicalModuleName, QString canonicalName,
        SymbolPrototypeRecord record, int priority, QString providerId) {
    canonicalModuleName = canonicalModuleName.trimmed();
    canonicalName = canonicalName.trimmed();
    if (canonicalName.isEmpty() || !record.prototype() ||
        record.conventionName().isEmpty() ||
        (record.stackArgumentsSize() && *record.stackArgumentsSize() < 0))
    {
        return INVALID;
    }

    const Key key(canonicalModuleName, canonicalName);
    auto position = entries_.find(key);
    if (position == entries_.end()) {
        entries_.emplace(
            std::piecewise_construct,
            std::forward_as_tuple(key),
            std::forward_as_tuple(
                std::move(record), priority, std::move(providerId)));
        return ADDED;
    }

    Entry &entry = position->second;
    if (priority < entry.priority) {
        return IGNORED_LOWER_PRIORITY;
    }
    if (priority > entry.priority) {
        entry = Entry(std::move(record), priority, std::move(providerId));
        return REPLACED_LOWER_PRIORITY;
    }

    if (equivalentRecords(entry.record, record)) {
        if (providerId < entry.providerId) {
            entry.providerId = std::move(providerId);
        }
        return entry.conflicting ? CONFLICT : EQUIVALENT;
    }

    entry.conflicting = true;
    return CONFLICT;
}

void SymbolPrototypeRegistry::addProvider(
        const SymbolPrototypeProvider &provider,
        const SymbolPrototypeTarget &target) {
    const std::vector<NamedSymbolPrototype> prototypes =
        provider.getPrototypes(target);
    for (const NamedSymbolPrototype &prototype : prototypes) {
        add(prototype.moduleName(), prototype.name(), prototype.record(),
            provider.priority(), provider.id());
    }
}

const SymbolPrototypeRecord *SymbolPrototypeRegistry::lookup(
        const QString &canonicalModuleName,
        const QString &canonicalName) const {
    if (canonicalModuleName.isEmpty()) {
        return nullptr;
    }
    const auto qualified = entries_.find(
        Key(canonicalModuleName, canonicalName));
    return qualified == entries_.end() || qualified->second.conflicting ?
        nullptr : &qualified->second.record;
}

const SymbolPrototypeRecord *SymbolPrototypeRegistry::lookup(
        const QString &canonicalName) const {
    const auto position = entries_.find(Key(QString(), canonicalName));
    if (position == entries_.end() || position->second.conflicting) {
        return nullptr;
    }
    return &position->second.record;
}

bool SymbolPrototypeRegistry::hasConflict(
        const QString &canonicalModuleName,
        const QString &canonicalName) const {
    if (canonicalModuleName.isEmpty()) {
        return false;
    }
    const auto qualified = entries_.find(
        Key(canonicalModuleName, canonicalName));
    return qualified != entries_.end() && qualified->second.conflicting;
}

bool SymbolPrototypeRegistry::hasConflict(
        const QString &canonicalName) const {
    const auto position = entries_.find(Key(QString(), canonicalName));
    return position != entries_.end() && position->second.conflicting;
}

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
