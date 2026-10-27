/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <map>
#include <memory>
#include <utility>
#include <vector>

#include <boost/optional.hpp>

#include <QString>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

class FunctionPrototype;

/**
 * Checks the target-width invariants required by the scalar prototype model.
 *
 * This is a trust boundary for programmatic providers as well as JSON-backed
 * providers: integers must fit one ABI slot, pointers must match the target,
 * and nested callback parameters must remain pointer-typed scalar contracts.
 */
bool isFunctionPrototypeTargetCompatible(
    const FunctionPrototype &prototype, SmallBitSize targetBitness);

/** Target properties used by external symbol prototype providers. */
class SymbolPrototypeTarget {
    QString architecture_;
    QString operatingSystem_;
    SmallBitSize bitness_;

public:
    SymbolPrototypeTarget(QString architecture, QString operatingSystem,
                          SmallBitSize bitness):
        architecture_(std::move(architecture)),
        operatingSystem_(std::move(operatingSystem)), bitness_(bitness)
    {}

    const QString &architecture() const { return architecture_; }
    const QString &operatingSystem() const { return operatingSystem_; }
    SmallBitSize bitness() const { return bitness_; }
};

/**
 * ABI-resolved metadata for an external function.
 *
 * The prototype contains target-sized source types. The convention name is
 * the internal Architecture convention identifier, rather than a spelling
 * such as __stdcall. Stack argument size is optional because most ABIs do not
 * encode a fixed callee-pop byte count.
 */
class SymbolPrototypeRecord {
    std::shared_ptr<const FunctionPrototype> prototype_;
    QString conventionName_;
    boost::optional<ByteSize> stackArgumentsSize_;
    bool doesNotReturn_;

public:
    SymbolPrototypeRecord(
        std::shared_ptr<const FunctionPrototype> prototype,
        QString conventionName,
        boost::optional<ByteSize> stackArgumentsSize = boost::none,
        bool doesNotReturn = false):
        prototype_(std::move(prototype)),
        conventionName_(std::move(conventionName)),
        stackArgumentsSize_(stackArgumentsSize),
        doesNotReturn_(doesNotReturn)
    {}

    const std::shared_ptr<const FunctionPrototype> &prototype() const {
        return prototype_;
    }

    const QString &conventionName() const { return conventionName_; }

    const boost::optional<ByteSize> &stackArgumentsSize() const {
        return stackArgumentsSize_;
    }

    bool doesNotReturn() const { return doesNotReturn_; }
};

/** One canonical external symbol name and its target-specific metadata. */
class NamedSymbolPrototype {
    QString moduleName_;
    QString name_;
    SymbolPrototypeRecord record_;

public:
    NamedSymbolPrototype(QString name, SymbolPrototypeRecord record):
        name_(std::move(name)), record_(std::move(record))
    {}

    NamedSymbolPrototype(QString moduleName, QString name,
                         SymbolPrototypeRecord record):
        moduleName_(std::move(moduleName)), name_(std::move(name)),
        record_(std::move(record))
    {}

    const QString &moduleName() const { return moduleName_; }
    const QString &name() const { return name_; }
    const SymbolPrototypeRecord &record() const { return record_; }
};

/** Source of target-specific external symbol metadata. */
class SymbolPrototypeProvider {
public:
    virtual ~SymbolPrototypeProvider() {}

    /** Stable diagnostic identifier for deterministic collision handling. */
    virtual QString id() const = 0;

    /**
     * Provider precedence. Higher priorities replace lower priorities.
     * Conflicting records at the same priority make that name ambiguous.
     */
    virtual int priority() const = 0;

    virtual std::vector<NamedSymbolPrototype> getPrototypes(
        const SymbolPrototypeTarget &target) const = 0;
};

/**
 * Mergeable registry of canonical external symbol prototypes.
 *
 * Names are intentionally not normalized here. Object-format/debugger name
 * normalization belongs to the caller, which must pass a canonical external
 * symbol name. This prevents a platform-neutral registry from guessing about
 * namespaces, module separators, or decoration rules.
 */
class SymbolPrototypeRegistry {
public:
    enum AddResult {
        ADDED,
        REPLACED_LOWER_PRIORITY,
        EQUIVALENT,
        IGNORED_LOWER_PRIORITY,
        CONFLICT,
        INVALID
    };

private:
    struct Entry {
        SymbolPrototypeRecord record;
        int priority;
        QString providerId;
        bool conflicting;

        Entry(SymbolPrototypeRecord record, int priority, QString providerId):
            record(std::move(record)), priority(priority),
            providerId(std::move(providerId)), conflicting(false)
        {}
    };

    typedef std::pair<QString, QString> Key;
    std::map<Key, Entry> entries_;

public:
    /** Adds module-qualified metadata. An empty module is an explicit
     * provider-wide fallback and is never confused with a qualified entry. */
    AddResult add(QString canonicalModuleName, QString canonicalName,
                  SymbolPrototypeRecord record, int priority,
                  QString providerId);

    /** Backward-compatible shorthand for an unqualified provider entry. */
    AddResult add(QString canonicalName, SymbolPrototypeRecord record,
                  int priority, QString providerId) {
        return add(QString(), std::move(canonicalName), std::move(record),
                   priority, std::move(providerId));
    }

    void addProvider(const SymbolPrototypeProvider &provider,
                     const SymbolPrototypeTarget &target);

    /**
     * Returns only an exact module-qualified entry. An empty module is never
     * accepted on this semantic lookup path. Same-priority conflicts return
     * nullptr.
     */
    const SymbolPrototypeRecord *lookup(
        const QString &canonicalModuleName,
        const QString &canonicalName) const;

    /** Looks up only an explicitly unqualified provider entry. */
    const SymbolPrototypeRecord *lookup(const QString &canonicalName) const;

    /** Checks only an exact, non-empty module-qualified entry. */
    bool hasConflict(const QString &canonicalModuleName,
                     const QString &canonicalName) const;

    bool hasConflict(const QString &canonicalName) const;
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
