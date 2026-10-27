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

#include "DeclarationGenerator.h"

#include <nc/common/Foreach.h>
#include <nc/common/Unreachable.h>
#include <nc/common/make_unique.h>

#include <nc/core/image/Image.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/CallHook.h>
#include <nc/core/ir/calling/EntryHook.h>
#include <nc/core/ir/calling/FunctionSignature.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/ReturnHook.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/types/Types.h>
#include <nc/core/likec/FunctionDeclaration.h>
#include <nc/core/likec/Tree.h>

namespace nc {
namespace core {
namespace ir {
namespace cgen {

const likec::Type *DeclarationGenerator::makePresentationType(
        const calling::TypeDescription &description) {
    switch (description.kind()) {
        case calling::TypeDescription::VOID:
            return tree().makeVoidType();
        case calling::TypeDescription::INTEGER:
            return tree().makeIntegerType(
                description.size(), description.isUnsigned(), description.displayName());
        case calling::TypeDescription::POINTER:
            return tree().makePointerType(
                description.size(), tree().makeVoidType(), description.displayName());
    }

    unreachable();
    return tree().makeErroneousType();
}

DeclarationGenerator::DeclarationGenerator(
        CodeGenerator &parent,
        const calling::CalleeId &calleeId,
        const calling::FunctionSignature *signature,
        bool usePrototypeTypes):
    parent_(parent),
    calleeId_(calleeId),
    signature_(signature),
    usePrototypeTypes_(usePrototypeTypes),
    declaration_(nullptr)
{
    assert(signature != nullptr);
}

void DeclarationGenerator::setDeclaration(likec::FunctionDeclaration *declaration) {
    assert(!declaration_); 
    declaration_ = declaration;
    if (signature()->prototype()) {
        declaration_->setCallingConvention(signature()->prototype()->callingConvention());
    }
    parent().setFunctionDeclaration(signature_, declaration);
}

std::unique_ptr<likec::FunctionDeclaration> DeclarationGenerator::createDeclaration() {
    auto nameAndComment = parent().nameGenerator().getFunctionName(calleeId_);
    if (signature()->prototype() && !signature()->prototype()->preferredName().isEmpty()) {
        nameAndComment.name() = signature()->prototype()->preferredName();
    }
    nameAndComment.name() = parent().getFunctionIdentifier(
        signature(), nameAndComment.name());

    auto functionDeclaration = std::make_unique<likec::FunctionDeclaration>(tree(),
        std::move(nameAndComment.name()), makeReturnType(), signature()->variadic());
    functionDeclaration->setComment(std::move(nameAndComment.comment()));

    setDeclaration(functionDeclaration.get());

    foreach (const auto &argument, signature()->arguments()) {
        makeArgumentDeclaration(argument.get());
    }

    return functionDeclaration;
}

const likec::Type *DeclarationGenerator::makeReturnType() {
    if (usePrototypeTypes_ && signature()->prototype()) {
        return makePresentationType(signature()->prototype()->returnType());
    }
    if (signature()->returnValue()) {
        return parent().makeType(parent().types().getType(signature()->returnValue().get()));
    }
    return tree().makeVoidType();
}

likec::ArgumentDeclaration *DeclarationGenerator::makeArgumentDeclaration(const Term *term) {
    const std::size_t index = declaration()->arguments().size();
    auto nameAndComment = parent().nameGenerator().getArgumentName(term, index + 1);
    const likec::Type *type = parent().makeType(parent().types().getType(term));

    if (signature()->prototype() && index < signature()->prototype()->parameters().size()) {
        const auto &parameter = signature()->prototype()->parameters()[index];
        if (!parameter.name().isEmpty()) {
            nameAndComment.name() = parameter.name();
        }
        if (usePrototypeTypes_) {
            type = makePresentationType(parameter.type());
        }
    }
    nameAndComment.name() = claimLocalIdentifier(nameAndComment.name());

    auto argumentDeclaration = std::make_unique<likec::ArgumentDeclaration>(
        std::move(nameAndComment.name()), type);
    argumentDeclaration->setComment(std::move(nameAndComment.comment()));

    auto result = argumentDeclaration.get();
    declaration()->addArgument(std::move(argumentDeclaration));

    return result;
}

QString DeclarationGenerator::claimLocalIdentifier(
        const QString &candidate) {
    return parent().claimLocalIdentifier(candidate, localIdentifiers_);
}

} // namespace cgen
} // namespace ir
} // namespace core
} // namespace nc

/* vim:set et sts=4 sw=4: */
