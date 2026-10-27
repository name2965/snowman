/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#pragma once

#include <nc/config.h>

#include <memory>
#include <utility>
#include <vector>

#include <QString>

#include <nc/common/Types.h>

namespace nc {
namespace core {
namespace ir {
namespace calling {

class FunctionPrototype;

/**
 * Source-level type information attached to a recovered signature.
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
public:
    /** Conservative effects on memory reachable through one argument. */
    enum class PointeeAccess {
        NONE,
        READ,
        WRITE,
        READ_WRITE
    };

private:
    QString name_;
    TypeDescription type_;
    PointeeAccess pointeeAccess_;
    std::shared_ptr<const FunctionPrototype> callbackPrototype_;

public:
    /**
     * Backward-compatible constructor. Historical metadata described only
     * writes, so a non-writable parameter remains conservatively readable.
     */
    ParameterDescription(
            QString name, TypeDescription type, bool mayWriteMemory = true,
            std::shared_ptr<const FunctionPrototype> callbackPrototype =
                std::shared_ptr<const FunctionPrototype>()):
        name_(std::move(name)), type_(std::move(type)),
        pointeeAccess_(mayWriteMemory ? PointeeAccess::READ_WRITE :
                                       PointeeAccess::READ),
        callbackPrototype_(std::move(callbackPrototype))
    {}

    ParameterDescription(
            QString name, TypeDescription type, PointeeAccess pointeeAccess,
            std::shared_ptr<const FunctionPrototype> callbackPrototype =
                std::shared_ptr<const FunctionPrototype>()):
        name_(std::move(name)), type_(std::move(type)),
        pointeeAccess_(pointeeAccess),
        callbackPrototype_(std::move(callbackPrototype))
    {}

    const QString &name() const { return name_; }
    const TypeDescription &type() const { return type_; }

    /**
     * \return True if the callee may observe memory reachable through this
     *         argument. This effect is independent of whether that memory can
     *         also be modified.
     */
    bool mayReadMemory() const {
        return pointeeAccess_ == PointeeAccess::READ ||
               pointeeAccess_ == PointeeAccess::READ_WRITE;
    }

    /**
     * \return True if the callee may modify memory reachable through this
     *         argument. This is conservative by default for prototypes which
     *         do not provide const/output metadata.
     */
    bool mayWriteMemory() const {
        return pointeeAccess_ == PointeeAccess::WRITE ||
               pointeeAccess_ == PointeeAccess::READ_WRITE;
    }

    PointeeAccess pointeeAccess() const { return pointeeAccess_; }

    /**
     * \return Prototype of the function accepted by this parameter, or an
     *         empty pointer when the parameter is not a known callback.
     *
     * This metadata is independent of the parameter's source-level typedef
     * spelling. For example, two different callback typedef names may share
     * the same nested function prototype.
     */
    const std::shared_ptr<const FunctionPrototype> &callbackPrototype() const {
        return callbackPrototype_;
    }
};

/**
 * Optional source-level and semantic metadata for a recovered function
 * signature. In addition to presentation names, parameter descriptions carry
 * memory-effect and nested callback information used by analysis passes.
 */
class FunctionPrototype {
    TypeDescription returnType_;
    std::vector<ParameterDescription> parameters_;
    QString callingConvention_; ///< Optional source-level declaration spelling.
    QString preferredName_;
    bool memoryEffectsAreComplete_;
    QString abiConventionName_; ///< Internal Architecture ABI id for callbacks.
    bool variadic_;

public:
    /**
     * \param memoryEffectsAreComplete True only when the per-parameter
     *        PointeeAccess values are a complete summary of memory reachable
     *        from the caller, including the absence of accesses through
     *        globals, captured callbacks, or previously escaped pointers.
     *        The conservative default is false: a declaration alone does not
     *        prove that unmentioned memory is untouched.
     */
    FunctionPrototype(TypeDescription returnType,
                      std::vector<ParameterDescription> parameters = std::vector<ParameterDescription>(),
                      QString callingConvention = QString(),
                      QString preferredName = QString(),
                      bool memoryEffectsAreComplete = false,
                      QString abiConventionName = QString(),
                      bool variadic = false):
        returnType_(std::move(returnType)),
        parameters_(std::move(parameters)),
        callingConvention_(std::move(callingConvention)),
        preferredName_(std::move(preferredName)),
        memoryEffectsAreComplete_(memoryEffectsAreComplete),
        abiConventionName_(std::move(abiConventionName)),
        variadic_(variadic)
    {}

    const TypeDescription &returnType() const { return returnType_; }
    const std::vector<ParameterDescription> &parameters() const { return parameters_; }
    const QString &callingConvention() const { return callingConvention_; }
    const QString &preferredName() const { return preferredName_; }

    /** Internal target Architecture convention identifier for callbacks. */
    const QString &abiConventionName() const { return abiConventionName_; }

    /** Whether calls can carry arguments beyond the fixed parameter prefix. */
    bool variadic() const { return variadic_; }

    /** Whether parameter effects exclude all other caller-memory accesses. */
    bool memoryEffectsAreComplete() const {
        return memoryEffectsAreComplete_;
    }
};

/**
 * Compares every semantic and presentation field of two prototypes,
 * including nested callback contracts.
 */
bool areFunctionPrototypesEquivalent(
    const FunctionPrototype &left, const FunctionPrototype &right);

} // namespace calling
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
