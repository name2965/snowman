/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include <QByteArray>
#include <QString>

#include "SymbolPrototypeRegistry.h"

namespace nc {
namespace core {
namespace ir {
namespace calling {

/**
 * Target-specific symbol prototypes loaded from a versioned JSON document.
 *
 * The parser deliberately performs no name canonicalization. Module and
 * symbol names are exact registry keys, and target selection is an exact
 * match on architecture, operating system and bitness. A document is accepted
 * only as a whole: an unsupported version, unknown member, duplicate key, or
 * invalid record makes fromJson() return an empty pointer.
 *
 * Metadata generators must emit module and symbol keys in the canonical form
 * expected by the platform-specific lookup path. The provider never guesses
 * aliases or changes case. In particular, Windows generators must emit the
 * exact lower-case import-descriptor module name (including its suffix) used
 * by canonicalWindowsExternalModuleName(). Empty keys and keys with
 * surrounding whitespace are rejected rather than normalized.
 */
class DeclarativeSymbolPrototypeProvider: public SymbolPrototypeProvider {
public:
    /** Parsed storage record; public only to keep the parser implementation
     * independent of Boost.PropertyTree in this header. */
    struct TargetRecords {
        QString architecture;
        QString operatingSystem;
        SmallBitSize bitness;
        std::vector<NamedSymbolPrototype> prototypes;

        TargetRecords(QString architecture, QString operatingSystem,
                      SmallBitSize bitness,
                      std::vector<NamedSymbolPrototype> prototypes):
            architecture(std::move(architecture)),
            operatingSystem(std::move(operatingSystem)), bitness(bitness),
            prototypes(std::move(prototypes))
        {}
    };

private:
    QString id_;
    int priority_;
    std::vector<TargetRecords> targets_;

    DeclarativeSymbolPrototypeProvider(
        QString id, int priority, std::vector<TargetRecords> targets):
        id_(std::move(id)), priority_(priority), targets_(std::move(targets))
    {}

public:
    /** Stable schema identifier accepted by this implementation. */
    static const char *schemaName();

    /** Currently supported schema version. */
    static int schemaVersion();

    /**
     * Parses a UTF-8 JSON document. On failure, returns an empty pointer and
     * optionally stores a diagnostic. No records from a rejected document are
     * retained.
     */
    static std::shared_ptr<const DeclarativeSymbolPrototypeProvider> fromJson(
        const std::string &json, QString *error = nullptr);

    /** QByteArray convenience overload for Qt resources and files. */
    static std::shared_ptr<const DeclarativeSymbolPrototypeProvider> fromJson(
        const QByteArray &json, QString *error = nullptr);

    QString id() const override { return id_; }
    int priority() const override { return priority_; }

    std::vector<NamedSymbolPrototype> getPrototypes(
        const SymbolPrototypeTarget &target) const override;

    /** Number of records selected by an exact target, without copying the
     * (potentially large) generated catalog. Intended for deployment and
     * loader diagnostics. */
    std::size_t prototypeCount(
        const SymbolPrototypeTarget &target) const;
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
