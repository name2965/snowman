/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <boost/optional.hpp>

#include <QCoreApplication>
#include <QString>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace image {

class Section;

/**
 * Provenance of an external symbol's spelling.
 *
 * Object-format names participate in linking exactly as stored and therefore
 * must never have debugger decorations stripped from them. Debugger display
 * names may contain presentation-only wrappers such as "<JMP.&...>".
 */
enum class ExternalNameOrigin {
    UNKNOWN,
    OBJECT_FILE,
    DEBUGGER
};

/**
 * Symbol type.
 */
class SymbolType {
    Q_DECLARE_TR_FUNCTIONS(SymbolType)

public:
    /**
     * Symbol type values.
     */
    enum Type {
        NOTYPE,   ///< Not specified or unknown.
        FUNCTION, ///< Function.
        OBJECT,   ///< Data object.
        SECTION   ///< Section object.
    };

    /**
     * Constructor.
     *
     * \param type Symbol type value.
     */
    SymbolType(Type type = NOTYPE): type_(type) {}

    /**
     * \return Symbol type value.
     */
    operator Type() const { return type_; }

    /**
     * \param type Symbol type value.
     *
     * \return Name of the given symbol type.
     */
    static QString getName(Type type);

    /**
     * \return Name of the symbol type.
     */
    QString getName() const { return getName(type_); }

private:
    Type type_;
};

class Symbol {
private:
    SymbolType type_; ///< Type of the symbol.
    QString name_; ///< Name of the symbol.
    boost::optional<ConstantValue> value_; ///< Value of the symbol.
    const Section *section_; ///< Section referenced by the symbol.
    QString moduleName_; ///< Source module for an imported symbol, if known.
    ExternalNameOrigin externalNameOrigin_; ///< Provenance of an external name.

public:
    /**
     * Constructor.
     *
     * \param type Type of the symbol.
     * \param name Name of the symbol.
     * \param value Value of the symbol.
     * \param section Pointer to the section referenced by the symbol.
     * \param moduleName Source module for an imported symbol, if known.
     * \param externalNameOrigin Provenance of the external symbol spelling.
     */
    Symbol(SymbolType type, QString name,
           const boost::optional<ConstantValue> &value,
           const Section *section = nullptr, QString moduleName = QString(),
           ExternalNameOrigin externalNameOrigin = ExternalNameOrigin::UNKNOWN):
        type_(type), name_(std::move(name)), value_(value), section_(section),
        moduleName_(std::move(moduleName)),
        externalNameOrigin_(externalNameOrigin)
    {}

    /**
     * \return Type of the symbol.
     */
    SymbolType type() const { return type_; }

    /**
     * \return Name of the symbol.
     */
    QString name() const { return name_; }

    /**
     * \return Value of the symbol.
     */
    const boost::optional<ConstantValue> &value() const { return value_; }

    /**
     * \return Pointer to the section references by the symbol. Can be nullptr.
     */
    const Section *section() const { return section_; }

    /**
     * \return Source module for an imported symbol, or an empty string when
     *         the object format/debugger did not preserve that identity.
     */
    const QString &moduleName() const { return moduleName_; }

    /**
     * \return Provenance used to decide whether presentation decorations may
     *         be removed during an external prototype lookup.
     */
    ExternalNameOrigin externalNameOrigin() const {
        return externalNameOrigin_;
    }
};

} // namespace image
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
