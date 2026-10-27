/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <memory>
#include <stdexcept>
#include <vector>

#include <nc/common/CancellationToken.h>
#include <nc/common/SizedValue.h>
#include <nc/core/image/Image.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Functions.h>
#include <nc/core/ir/MemoryDomain.h>
#include <nc/core/ir/MemoryLocation.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/calling/Conventions.h>
#include <nc/core/ir/calling/FunctionSignature.h>
#include <nc/core/ir/calling/Hooks.h>
#include <nc/core/ir/calling/Signatures.h>
#include <nc/core/ir/cflow/Graph.h>
#include <nc/core/ir/cflow/GraphBuilder.h>
#include <nc/core/ir/cflow/Graphs.h>
#include <nc/core/ir/cgen/CodeGenerator.h>
#include <nc/core/ir/cgen/DefinitionGenerator.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DataflowStatus.h>
#include <nc/core/ir/dflow/Dataflows.h>
#include <nc/core/ir/idiom/Idioms.h>
#include <nc/core/ir/liveness/Liveness.h>
#include <nc/core/ir/liveness/Livenesses.h>
#include <nc/core/ir/types/Types.h>
#include <nc/core/ir/vars/Variable.h>
#include <nc/core/ir/vars/Variables.h>
#include <nc/core/likec/Block.h>
#include <nc/core/likec/FunctionDefinition.h>
#include <nc/core/likec/Tree.h>

using namespace nc;
using namespace nc::core;
using namespace nc::core::ir;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

bool generateAndFindSourceWrite(bool addOrdinaryUse,
                                bool requireMaterialization) {
    const MemoryLocation sourceLocation(MemoryDomain::STACK, -64, 32);
    const MemoryLocation resultLocation(MemoryDomain::STACK, -128, 32);

    Function function;
    std::unique_ptr<BasicBlock> blockStorage(new BasicBlock());
    BasicBlock *block = blockStorage.get();
    function.addBasicBlock(std::move(blockStorage));
    function.setEntry(block);

    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(sourceLocation));
    Term *write = destination.get();
    std::unique_ptr<Statement> assignmentStorage(new Assignment(
        std::move(destination),
        std::unique_ptr<Term>(new Constant(SizedValue(32, 0x2a)))));
    const Statement *assignment = assignmentStorage.get();
    block->pushBack(std::move(assignmentStorage));

    Term *read = nullptr;
    Term *resultWrite = nullptr;
    if (addOrdinaryUse) {
        std::unique_ptr<Term> readStorage(
            new MemoryLocationAccess(sourceLocation));
        read = readStorage.get();
        std::unique_ptr<Term> resultDestination(
            new MemoryLocationAccess(resultLocation));
        resultWrite = resultDestination.get();
        block->pushBack(std::unique_ptr<Statement>(new Assignment(
            std::move(resultDestination), std::move(readStorage))));
    }

    std::unique_ptr<dflow::Dataflow> dataflow(new dflow::Dataflow());
    dataflow->setMemoryLocation(write, sourceLocation);
    if (read) {
        dataflow->setMemoryLocation(read, sourceLocation);
        dataflow->setMemoryLocation(resultWrite, resultLocation);
        dataflow->getDefinitions(read).addDefinition(sourceLocation, write);
    }
    dataflow->setAnalysisStatus(dflow::DataflowStatus::CONVERGED);

    std::unique_ptr<liveness::Liveness> liveness(
        new liveness::Liveness());
    liveness->makeLive(write);
    if (requireMaterialization) {
        liveness->requireMaterialization(write);
    }
    if (read) {
        liveness->makeLive(read);
        liveness->makeLive(resultWrite);
    }

    std::vector<vars::Variable::TermAndLocation> sourceVariableTerms;
    sourceVariableTerms.push_back(
        vars::Variable::TermAndLocation(write, sourceLocation));
    if (read) {
        sourceVariableTerms.push_back(
            vars::Variable::TermAndLocation(read, sourceLocation));
    }

    vars::Variables variables;
    variables.addVariable(std::unique_ptr<vars::Variable>(
        new vars::Variable(vars::Variable::LOCAL,
                           std::move(sourceVariableTerms), sourceLocation)));
    if (resultWrite) {
        std::vector<vars::Variable::TermAndLocation> resultVariableTerms;
        resultVariableTerms.push_back(
            vars::Variable::TermAndLocation(resultWrite, resultLocation));
        variables.addVariable(std::unique_ptr<vars::Variable>(
            new vars::Variable(vars::Variable::LOCAL,
                               std::move(resultVariableTerms),
                               resultLocation)));
    }

    std::unique_ptr<cflow::Graph> graph(new cflow::Graph());
    cflow::GraphBuilder()(*graph, &function);

    dflow::Dataflows dataflows;
    dataflows[&function] = std::move(dataflow);

    cflow::Graphs graphs;
    graphs[&function] = std::move(graph);

    liveness::Livenesses livenesses;
    livenesses[&function] = std::move(liveness);

    idiom::Idioms idioms;
    idioms[&function] = std::unique_ptr<const idiom::FunctionIdioms>(
        new idiom::FunctionIdioms());

    calling::Signatures signatures;
    signatures.setSignature(
        &function, std::shared_ptr<calling::FunctionSignature>(
            new calling::FunctionSignature()));
    calling::Conventions conventions;
    calling::Hooks hooks(conventions, signatures);

    likec::Tree tree;
    image::Image image;
    Functions functions;
    types::Types types;
    CancellationToken canceled;

    cgen::CodeGenerator codeGenerator(
        tree, image, functions, hooks, signatures, dataflows, variables,
        graphs, livenesses, idioms, types, canceled);
    cgen::DefinitionGenerator definitionGenerator(
        codeGenerator, &function, canceled);
    std::unique_ptr<likec::FunctionDefinition> definition =
        definitionGenerator.createDefinition();

    const likec::Block *definitionBlock = definition->block().get();
    for (const likec::Statement *statementNode :
         definitionBlock->statements())
    {
        if (statementNode->statement() == assignment) {
            return true;
        }
    }

    return false;
}

void testLiveWriteWithoutTermUseIsPreserved() {
    /*
     * Liveness is an independent property: even if no ordinary read was
     * recorded, code generation must fail closed and retain a live write.
     */
    check(generateAndFindSourceWrite(false, false),
          "a live write without an ordinary read use must be emitted");
}

void testSnapshotObservedWriteIsPreserved() {
    /* A semantic memory snapshot observes a write without creating a read. */
    check(generateAndFindSourceWrite(false, true),
          "a snapshot-observed write without an ordinary use must be emitted");
}

void testSnapshotObservedWriteWithOrdinaryUseIsPreserved() {
    /*
     * The ordinary read remains eligible for normal expression generation,
     * but it must not cause a snapshot-observed definition to disappear from
     * its original program point.
     */
    check(generateAndFindSourceWrite(true, true),
          "a snapshot-observed write with an ordinary use must be emitted");
}

} // anonymous namespace

int main() {
    try {
        testLiveWriteWithoutTermUseIsPreserved();
        testSnapshotObservedWriteIsPreserved();
        testSnapshotObservedWriteWithOrdinaryUseIsPreserved();
    } catch (const std::exception &exception) {
        std::cerr << "definition-generator regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
