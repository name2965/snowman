/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include "SymbolPrototypeRegistry.h"

#include <cstddef>
#include <functional>
#include <map>
#include <set>
#include <tuple>
#include <utility>

#include "FunctionPrototype.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

namespace {

const std::size_t MAX_PROVIDER_PARAMETERS = 1024;
const unsigned int MAX_PROVIDER_CALLBACK_DEPTH = 16;
const std::size_t MAX_PROVIDER_UNIQUE_PROTOTYPES = 4096;
const std::size_t MAX_PROVIDER_PARAMETER_VISITS = 65536;
const std::size_t MAX_EQUIVALENCE_PROTOTYPE_PAIRS = 65536;
const std::size_t MAX_EQUIVALENCE_PARAMETER_COMPARISONS = 262144;
const unsigned int MAX_EQUIVALENCE_CALLBACK_DEPTH =
    MAX_PROVIDER_CALLBACK_DEPTH;

bool isTypeTargetCompatible(
        const TypeDescription &type, SmallBitSize targetBitness,
        bool allowVoid) {
    if (targetBitness <= 0) {
        return false;
    }

    switch (type.kind()) {
    case TypeDescription::VOID:
        return allowVoid && type.size() == 0 && !type.isUnsigned();
    case TypeDescription::INTEGER:
        return type.size() > 0 && type.size() <= targetBitness;
    case TypeDescription::POINTER:
        return type.size() == targetBitness && type.isUnsigned();
    }
    return false;
}

bool isPointeeAccessValid(
        ParameterDescription::PointeeAccess access) {
    switch (access) {
    case ParameterDescription::PointeeAccess::NONE:
    case ParameterDescription::PointeeAccess::READ:
    case ParameterDescription::PointeeAccess::WRITE:
    case ParameterDescription::PointeeAccess::READ_WRITE:
        return true;
    }
    return false;
}

typedef std::pair<const FunctionPrototype *, unsigned int> PrototypeDepth;

struct PrototypeDepthLess {
    bool operator()(const PrototypeDepth &left,
                    const PrototypeDepth &right) const {
        std::less<const FunctionPrototype *> less;
        if (less(left.first, right.first)) {
            return true;
        }
        if (less(right.first, left.first)) {
            return false;
        }
        return left.second < right.second;
    }
};

struct TargetCompatibilityCache {
    std::map<PrototypeDepth, bool, PrototypeDepthLess> results;
};

struct TargetCompatibilityTraversal {
    TargetCompatibilityCache &cache;
    std::set<const FunctionPrototype *,
             std::less<const FunctionPrototype *>> active;
    std::set<const FunctionPrototype *,
             std::less<const FunctionPrototype *>> unique;
    std::size_t parameterVisits = 0;

    explicit TargetCompatibilityTraversal(
            TargetCompatibilityCache &cache): cache(cache) {}
};

bool isFunctionPrototypeTargetCompatibleImpl(
        const FunctionPrototype &prototype, SmallBitSize targetBitness,
        unsigned int callbackDepth,
        TargetCompatibilityTraversal &traversal) {
    const PrototypeDepth key(&prototype, callbackDepth);
    const auto known = traversal.cache.results.find(key);
    if (known != traversal.cache.results.end()) {
        return known->second;
    }

    bool compatible =
        callbackDepth <= MAX_PROVIDER_CALLBACK_DEPTH &&
        prototype.parameters().size() <= MAX_PROVIDER_PARAMETERS &&
        isTypeTargetCompatible(prototype.returnType(), targetBitness, true);

    if (compatible && traversal.unique.insert(&prototype).second &&
        traversal.unique.size() > MAX_PROVIDER_UNIQUE_PROTOTYPES)
    {
        compatible = false;
    }
    if (compatible &&
        prototype.parameters().size() >
            MAX_PROVIDER_PARAMETER_VISITS - traversal.parameterVisits)
    {
        compatible = false;
    }
    if (compatible) {
        traversal.parameterVisits += prototype.parameters().size();
    }

    /* FunctionPrototype is immutable through its public API, but reject a
     * cyclic graph defensively in case a programmatic provider manufactured
     * one through aliasing or const-casts. */
    if (compatible && !traversal.active.insert(&prototype).second) {
        compatible = false;
    }

    if (compatible) {
        for (const ParameterDescription &parameter : prototype.parameters()) {
            const TypeDescription &type = parameter.type();
            if (!isTypeTargetCompatible(type, targetBitness, false) ||
                !isPointeeAccessValid(parameter.pointeeAccess()) ||
                (type.kind() != TypeDescription::POINTER &&
                 parameter.pointeeAccess() !=
                    ParameterDescription::PointeeAccess::NONE))
            {
                compatible = false;
                break;
            }

            const auto &callback = parameter.callbackPrototype();
            if (callback &&
                (type.kind() != TypeDescription::POINTER ||
                 callback->abiConventionName().isEmpty() ||
                 !isFunctionPrototypeTargetCompatibleImpl(
                    *callback, targetBitness, callbackDepth + 1,
                    traversal)))
            {
                compatible = false;
                break;
            }
        }
        traversal.active.erase(&prototype);
    }

    traversal.cache.results.emplace(key, compatible);
    return compatible;
}

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

struct PrototypeEquivalenceTraversal {
    std::set<PrototypePair, PrototypePairLess> visited;
    std::size_t parameterComparisons = 0;
};

bool equivalentPrototypesImpl(
        const FunctionPrototype &left, const FunctionPrototype &right,
        PrototypeEquivalenceTraversal &traversal,
        unsigned int callbackDepth) {
    if (&left == &right) {
        return true;
    }
    if (callbackDepth > MAX_EQUIVALENCE_CALLBACK_DEPTH) {
        return false;
    }

    const PrototypePair pair(&left, &right);
    if (traversal.visited.find(pair) != traversal.visited.end()) {
        return true;
    }
    if (traversal.visited.size() >=
            MAX_EQUIVALENCE_PROTOTYPE_PAIRS)
    {
        return false;
    }
    traversal.visited.insert(pair);

    if (left.returnType() != right.returnType() ||
        left.callingConvention() != right.callingConvention() ||
        left.abiConventionName() != right.abiConventionName() ||
        left.variadic() != right.variadic() ||
        left.preferredName() != right.preferredName() ||
        left.memoryEffectsAreComplete() !=
            right.memoryEffectsAreComplete() ||
        left.parameters().size() != right.parameters().size())
    {
        return false;
    }
    if (left.parameters().size() >
        MAX_EQUIVALENCE_PARAMETER_COMPARISONS -
            traversal.parameterComparisons)
    {
        return false;
    }
    traversal.parameterComparisons += left.parameters().size();

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
        if (leftCallback && !equivalentPrototypesImpl(
                *leftCallback, *rightCallback, traversal,
                callbackDepth + 1))
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

    return areFunctionPrototypesEquivalent(
        *left.prototype(), *right.prototype());
}

} // anonymous namespace

bool isFunctionPrototypeTargetCompatible(
        const FunctionPrototype &prototype, SmallBitSize targetBitness) {
    TargetCompatibilityCache cache;
    TargetCompatibilityTraversal traversal(cache);
    return isFunctionPrototypeTargetCompatibleImpl(
        prototype, targetBitness, 0, traversal);
}

bool areFunctionPrototypesEquivalent(
        const FunctionPrototype &left, const FunctionPrototype &right) {
    PrototypeEquivalenceTraversal traversal;
    return equivalentPrototypesImpl(left, right, traversal, 0);
}

SymbolPrototypeRegistry::AddResult SymbolPrototypeRegistry::add(
        QString canonicalModuleName, QString canonicalName,
        SymbolPrototypeRecord record, int priority, QString providerId) {
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
        /* Resource limits apply independently to each public record. Reusing
         * a boolean cache across records would also reuse neither record's
         * unique-node nor parameter-visit footprint, allowing a later root
         * to combine many previously cached subgraphs past those limits. */
        TargetCompatibilityCache cache;
        TargetCompatibilityTraversal traversal(cache);
        if (!prototype.record().prototype() ||
            !isFunctionPrototypeTargetCompatibleImpl(
                *prototype.record().prototype(), target.bitness(), 0,
                traversal))
        {
            continue;
        }
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
