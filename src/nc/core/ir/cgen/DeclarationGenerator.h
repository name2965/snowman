/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

/* * SmartDec decompiler - SmartDec is a native code to C/C++ decompiler
 * Copyright (C) 2015 Alexander Chernov, Katerina Troshina, Yegor Derevenets,
 * Alexander Fokin, Sergey Levin, Leonid Tsvetkov
 *
 * This file is part of SmartDec decompiler.
 *
 * SmartDec decompiler is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SmartDec decompiler is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SmartDec decompiler.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include <nc/config.h>

#include <set>

#include <boost/noncopyable.hpp>

#include <nc/core/ir/calling/CalleeId.h>

#include "CodeGenerator.h"

namespace nc {
namespace core {

namespace likec {
    class ArgumentDeclaration;
    class FunctionDeclaration;
    class Tree;
}

namespace ir {

class Term;

namespace calling {
    class FunctionSignature;
    class TypeDescription;
}

namespace cgen {

/**
 * Generator of function declarations.
 */
class DeclarationGenerator: boost::noncopyable {
    CodeGenerator &parent_;
    calling::CalleeId calleeId_;
    const calling::FunctionSignature *signature_;
    bool usePrototypeTypes_;
    likec::FunctionDeclaration *declaration_;
    std::set<QString> localIdentifiers_;

public:
    /**
     * Constructor.
     *
     * \param parent Parent code generator.
     * \param calleeId Id of the function.
     * \param signature Valid pointer to the function's signature.
     */
    DeclarationGenerator(CodeGenerator &parent,
                         const calling::CalleeId &calleeId,
                         const calling::FunctionSignature *signature,
                         bool usePrototypeTypes = true);

    /**
     * Virtual destructor.
     */
    virtual ~DeclarationGenerator() {}

    /**
     * \return Parent code generator.
     */
    CodeGenerator &parent() const { return parent_; }

    /**
     * \return LikeC tree.
     */
    likec::Tree &tree() const { return parent().tree(); }

    /**
     * \return Pointer to the signature of the function, for which
     *         declaration is generated. Can be nullptr.
     */
    const calling::FunctionSignature *signature() const { return signature_; }

    /**
     * \return Function's declaration.
     */
    likec::FunctionDeclaration *declaration() const { return declaration_; }

    /**
     * Sets function's declaration without taking ownership of it.
     *
     * \param[in] declaration Function's declaration.
     */
    void setDeclaration(likec::FunctionDeclaration *declaration);

    /**
     * Creates function's declaration and sets function's declaration to it.
     *
     * \return Valid pointer to the created declaration.
     */
    std::unique_ptr<likec::FunctionDeclaration> createDeclaration();

protected:
    /**
     * \return Type of function's return value.
     */
    const likec::Type *makeReturnType();

    /**
     * Converts presentation metadata into a LikeC type without losing its
     * integer/pointer kind.
     */
    const likec::Type *makePresentationType(const calling::TypeDescription &description);

    /**
     * \return Whether the function has variable number of arguments.
     */
    bool variadic() const;

    /**
     * Creates the declaration of a function's argument.
     * Declaration is automatically added to the list of formal arguments
     * of current function's declaration.
     *
     * \param[in] term Valid pointer to the term representing the argument.
     *
     * \return Created declaration of function's argument.
     */
    likec::ArgumentDeclaration *makeArgumentDeclaration(const Term *term);

    /** Claims a collision-free identifier in the current function scope. */
    QString claimLocalIdentifier(const QString &candidate);
};

} // namespace cgen
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
