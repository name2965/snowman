/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <climits>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <vector>

#include <boost/optional.hpp>

#include <nc/arch/x86/X86Architecture.h>
#include <nc/common/CancellationToken.h>
#include <nc/core/image/Image.h>
#include <nc/core/image/Symbol.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/MemoryDomain.h>
#include <nc/core/ir/MemoryLocation.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/FunctionSignature.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cflow/Graphs.h>
#include <nc/core/ir/cgen/CodeGenerator.h>
#include <nc/core/ir/cgen/DeclarationGenerator.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/idiom/Idioms.h>
#include <nc/core/ir/liveness/Livenesses.h>
#include <nc/core/ir/types/Types.h>
#include <nc/core/ir/vars/Variable.h>
#include <nc/core/ir/vars/Variables.h>
#include <nc/core/likec/ArgumentDeclaration.h>
#include <nc/core/likec/FunctionDeclaration.h>
#include <nc/core/likec/Tree.h>

using namespace nc;
using namespace nc::core;
using namespace nc::core::ir;

namespace {

class IdentifierProbeDeclarationGenerator:
    public cgen::DeclarationGenerator {
public:
    IdentifierProbeDeclarationGenerator(
            cgen::CodeGenerator &parent,
            const calling::CalleeId &calleeId,
            const calling::FunctionSignature *signature):
        cgen::DeclarationGenerator(parent, calleeId, signature)
    {}

    QString claimLocalForTest(const QString &candidate) {
        return claimLocalIdentifier(candidate);
    }
};

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

std::shared_ptr<calling::FunctionSignature> makeNamedSignature(
        const QString &preferredName,
        const std::vector<QString> &parameterNames) {
    const calling::TypeDescription integerType(
        calling::TypeDescription::INTEGER, 32, false);
    std::vector<calling::ParameterDescription> parameters;
    auto signature = std::make_shared<calling::FunctionSignature>();

    for (std::size_t index = 0; index < parameterNames.size(); ++index) {
        parameters.push_back(calling::ParameterDescription(
            parameterNames[index], integerType, false));
        signature->arguments().push_back(
            std::make_shared<MemoryLocationAccess>(MemoryLocation(
                MemoryDomain::STACK,
                static_cast<BitAddr>(index * 32), 32)));
    }

    signature->setPrototype(std::make_shared<calling::FunctionPrototype>(
        calling::TypeDescription(
            calling::TypeDescription::VOID, 0, false),
        std::move(parameters), QString(), preferredName));
    return signature;
}

void testIdentifiersAreUniqueAndStableAcrossScopes() {
    likec::Tree tree;
    nc::arch::x86::X86Architecture architecture(
        nc::arch::x86::X86Architecture::PROTECTED_MODE);
    image::Image image;
    image.platform().setArchitecture(&architecture);
    image.addSymbol(std::unique_ptr<image::Symbol>(new image::Symbol(
        image::SymbolType::FUNCTION, QLatin1String("shared"),
        boost::optional<ConstantValue>(0x1000), nullptr,
        QLatin1String("module-a"))));
    image.addSymbol(std::unique_ptr<image::Symbol>(new image::Symbol(
        image::SymbolType::FUNCTION, QLatin1String("shared"),
        boost::optional<ConstantValue>(0x2000), nullptr,
        QLatin1String("module-b"))));

    Functions functions;
    types::Types types;
    vars::Variables variables;
    dflow::Dataflows dataflows;
    cflow::Graphs graphs;
    liveness::Livenesses livenesses;
    idiom::Idioms idioms;
    calling::Signatures signatures;
    calling::Conventions conventions;
    calling::Hooks hooks(conventions, signatures);
    CancellationToken canceled;
    cgen::CodeGenerator codeGenerator(
        tree, image, functions, hooks, signatures, dataflows, variables,
        graphs, livenesses, idioms, types, canceled);

    vars::Variable earlyGlobal(
        vars::Variable::GLOBAL,
        std::vector<vars::Variable::TermAndLocation>(),
        MemoryLocation(MemoryDomain::MEMORY, 0x3008 * CHAR_BIT, 32));
    check(codeGenerator.getVariableIdentifier(
              &earlyGlobal, QLatin1String("reserved")) ==
              QLatin1String("reserved"),
          "an uncontended global object must keep its preferred name");

    const auto firstSignature = makeNamedSignature(
        QLatin1String("shared"),
        std::vector<QString>{QLatin1String("item"),
                             QLatin1String("item"),
                             QLatin1String("reserved")});
    const auto secondSignature = makeNamedSignature(
        QLatin1String("shared"), std::vector<QString>());

    IdentifierProbeDeclarationGenerator firstGenerator(
        codeGenerator, calling::EntryAddress(0x1000),
        firstSignature.get());
    std::unique_ptr<likec::FunctionDeclaration> firstDeclaration =
        firstGenerator.createDeclaration();
    IdentifierProbeDeclarationGenerator secondGenerator(
        codeGenerator, calling::EntryAddress(0x2000),
        secondSignature.get());
    std::unique_ptr<likec::FunctionDeclaration> secondDeclaration =
        secondGenerator.createDeclaration();

    check(firstDeclaration->identifier() == QLatin1String("shared"),
          "the first module-qualified function must keep its leaf name");
    check(secondDeclaration->identifier() == QLatin1String("shared_2"),
          "equal leaf names from different modules must be uniquified");
    check(codeGenerator.getFunctionIdentifier(
              firstSignature.get(), QLatin1String("different")) ==
              firstDeclaration->identifier(),
          "a function identifier must remain stable after its first claim");

    check(firstDeclaration->arguments().size() == 3,
          "the identifier fixture must emit every formal parameter");
    check(firstDeclaration->arguments()[0]->identifier() ==
              QLatin1String("item") &&
          firstDeclaration->arguments()[1]->identifier() ==
              QLatin1String("item_2"),
          "duplicate formal names must be unique in their function scope");
    check(firstDeclaration->arguments()[2]->identifier() ==
              QLatin1String("reserved_2"),
          "a formal parameter must not shadow an existing global object");
    check(firstGenerator.claimLocalForTest(QLatin1String("item")) ==
              QLatin1String("item_3"),
          "a local must not collide with an existing formal parameter");

    vars::Variable collidingGlobal(
        vars::Variable::GLOBAL,
        std::vector<vars::Variable::TermAndLocation>(),
        MemoryLocation(MemoryDomain::MEMORY, 0x3000 * CHAR_BIT, 32));
    const QString globalIdentifier = codeGenerator.getVariableIdentifier(
        &collidingGlobal, QLatin1String("shared"));
    check(globalIdentifier == QLatin1String("shared_3"),
          "a global object must not collide with function identifiers");
    check(codeGenerator.getVariableIdentifier(
              &collidingGlobal, QLatin1String("different")) ==
              globalIdentifier,
          "a global object identifier must remain stable after its first claim");

    vars::Variable lateGlobal(
        vars::Variable::GLOBAL,
        std::vector<vars::Variable::TermAndLocation>(),
        MemoryLocation(MemoryDomain::MEMORY, 0x3004 * CHAR_BIT, 32));
    check(codeGenerator.getVariableIdentifier(
              &lateGlobal, QLatin1String("item")) ==
              QLatin1String("item_4"),
          "a lazily emitted global must not be shadowed by formals or locals");
}

} // anonymous namespace

int main() {
    try {
        testIdentifiersAreUniqueAndStableAcrossScopes();
    } catch (const std::exception &exception) {
        std::cerr << "cgen identifier regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
