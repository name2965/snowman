/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <utility>
#include <vector>

#include <QString>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

/**
 * Presentation-oriented type information attached to a recovered signature.
 *
 * The IR type analyzer deliberately keeps using structural integer and pointer
 * types. This description only supplies a more useful source-level spelling,
 * while preserving the same size, signedness and scalar kind in LikeC.
 */
class TypeDescription {
public:
    enum Kind {
        VOID,
        INTEGER,
        POINTER
    };

private:
    Kind kind_;
    SmallBitSize size_;
    bool isUnsigned_;
    QString displayName_;

public:
    TypeDescription(Kind kind, SmallBitSize size, bool isUnsigned, QString displayName = QString()):
        kind_(kind), size_(size), isUnsigned_(isUnsigned), displayName_(std::move(displayName))
    {}

    Kind kind() const { return kind_; }
    SmallBitSize size() const { return size_; }
    bool isUnsigned() const { return isUnsigned_; }
    const QString &displayName() const { return displayName_; }

    bool operator==(const TypeDescription &other) const {
        return kind() == other.kind() && size() == other.size() &&
               isUnsigned() == other.isUnsigned() && displayName() == other.displayName();
    }

    bool operator!=(const TypeDescription &other) const { return !(*this == other); }
};

/** Source-level name and type for a formal argument. */
class ParameterDescription {
    QString name_;
    TypeDescription type_;
    bool mayWriteMemory_;

public:
    ParameterDescription(QString name, TypeDescription type, bool mayWriteMemory = true):
        name_(std::move(name)), type_(std::move(type)), mayWriteMemory_(mayWriteMemory)
    {}

    const QString &name() const { return name_; }
    const TypeDescription &type() const { return type_; }

    /**
     * \return True if the callee may modify memory reachable through this
     *         argument. This is conservative by default for prototypes which
     *         do not provide const/output metadata.
     */
    bool mayWriteMemory() const { return mayWriteMemory_; }
};

/** Optional source-level metadata for a recovered function signature. */
class FunctionPrototype {
    TypeDescription returnType_;
    std::vector<ParameterDescription> parameters_;
    QString callingConvention_;
    QString preferredName_;

public:
    FunctionPrototype(TypeDescription returnType,
                      std::vector<ParameterDescription> parameters = std::vector<ParameterDescription>(),
                      QString callingConvention = QString(),
                      QString preferredName = QString()):
        returnType_(std::move(returnType)),
        parameters_(std::move(parameters)),
        callingConvention_(std::move(callingConvention)),
        preferredName_(std::move(preferredName))
    {}

    const TypeDescription &returnType() const { return returnType_; }
    const std::vector<ParameterDescription> &parameters() const { return parameters_; }
    const QString &callingConvention() const { return callingConvention_; }
    const QString &preferredName() const { return preferredName_; }
};

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
