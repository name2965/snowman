/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <memory>
#include <stdexcept>
#include <vector>

#include <nc/common/CancellationToken.h>
#include <nc/common/Foreach.h>
#include <nc/common/SizedValue.h>
#include <nc/core/ir/BasicBlock.h>
#include <nc/core/ir/CFG.h>
#include <nc/core/ir/Dominators.h>
#include <nc/core/ir/Function.h>
#include <nc/core/ir/Jump.h>
#include <nc/core/ir/PostDominators.h>
#include <nc/core/ir/Statements.h>
#include <nc/core/ir/Terms.h>
#include <nc/core/ir/cflow/BasicNode.h>
#include <nc/core/ir/cflow/Graph.h>
#include <nc/core/ir/cflow/GraphBuilder.h>
#include <nc/core/ir/cflow/Switch.h>
#include <nc/core/ir/cflow/StructureAnalyzer.h>
#include <nc/core/ir/dflow/AbstractValue.h>
#include <nc/core/ir/dflow/Dataflow.h>
#include <nc/core/ir/dflow/DefUseGraph.h>
#include <nc/core/ir/dflow/ExpressionIdentity.h>
#include <nc/core/ir/dflow/Value.h>
#include <nc/core/ir/dflow/ValueProvenance.h>
#include <nc/core/ir/misc/ArrayAccess.h>
#include <nc/core/ir/misc/PatternRecognition.h>

using namespace nc;
using namespace nc::core;
using namespace nc::core::ir;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

std::unique_ptr<Term> constant(SmallBitSize size, ConstantValue value) {
    return std::unique_ptr<Term>(
        new Constant(SizedValue(size, value)));
}

BasicBlock *addBlock(Function &function) {
    std::unique_ptr<BasicBlock> block(new BasicBlock());
    BasicBlock *result = block.get();
    function.addBasicBlock(std::move(block));
    return result;
}

std::unique_ptr<Term> locationAccess(
        const MemoryLocation &location, bool dereference) {
    if (dereference) {
        return std::unique_ptr<Term>(new Dereference(
            constant(32, 0x1000), MemoryDomain::MEMORY,
            location.size<SmallBitSize>()));
    }
    return std::unique_ptr<Term>(new MemoryLocationAccess(location));
}

Term *addDefinition(BasicBlock *block, const MemoryLocation &location,
                    std::unique_ptr<Term> source,
                    bool dereference = false) {
    std::unique_ptr<Term> destination =
        locationAccess(location, dereference);
    Term *definition = destination.get();
    block->pushBack(std::unique_ptr<Statement>(
        new Assignment(std::move(destination), std::move(source))));
    return definition;
}

struct DispatchTerms {
    Term *selectorRead;
    Term *temporaryDefinition;
    Term *temporaryRead;
    Term *flagDefinition;
    Term *flagRead;
};

DispatchTerms addCmpDispatch(
        BasicBlock *block, BasicBlock *caseTarget,
        BasicBlock *missTarget, ConstantValue caseValue,
        const MemoryLocation &selectorLocation,
        const MemoryLocation &temporaryLocation,
        const MemoryLocation &flagLocation, bool notEqualBranch,
        bool dereferenceSelector = false) {
    std::unique_ptr<Term> selector =
        locationAccess(selectorLocation, dereferenceSelector);
    Term *selectorRead = selector.get();
    std::unique_ptr<Term> difference(new BinaryOperator(
        BinaryOperator::SUB, std::move(selector),
        constant(32, caseValue), 32));
    Term *temporaryDefinition = addDefinition(
        block, temporaryLocation, std::move(difference));

    std::unique_ptr<Term> temporary(
        new MemoryLocationAccess(temporaryLocation));
    Term *temporaryRead = temporary.get();
    std::unique_ptr<Term> equality(new BinaryOperator(
        BinaryOperator::EQUAL, std::move(temporary),
        constant(32, 0), 1));
    Term *flagDefinition = addDefinition(
        block, flagLocation, std::move(equality));

    std::unique_ptr<Term> flag(
        new MemoryLocationAccess(flagLocation));
    Term *flagRead = flag.get();
    std::unique_ptr<Term> condition;
    if (notEqualBranch) {
        condition.reset(new UnaryOperator(
            UnaryOperator::NOT, std::move(flag), 1));
    } else {
        condition = std::move(flag);
    }
    block->pushBack(std::unique_ptr<Statement>(new Jump(
        std::move(condition), JumpTarget(caseTarget),
        JumpTarget(missTarget))));

    DispatchTerms result;
    result.selectorRead = selectorRead;
    result.temporaryDefinition = temporaryDefinition;
    result.temporaryRead = temporaryRead;
    result.flagDefinition = flagDefinition;
    result.flagRead = flagRead;
    return result;
}

Term *addDirectEqualityDispatch(
        BasicBlock *block, BasicBlock *caseTarget,
        BasicBlock *missTarget, ConstantValue caseValue,
        const MemoryLocation &selectorLocation,
        bool notEqualBranch = false) {
    std::unique_ptr<Term> selector(
        new MemoryLocationAccess(selectorLocation));
    Term *selectorRead = selector.get();
    std::unique_ptr<Term> condition(new BinaryOperator(
        BinaryOperator::EQUAL, std::move(selector),
        constant(32, caseValue), 1));
    if (notEqualBranch) {
        condition.reset(new UnaryOperator(
            UnaryOperator::NOT, std::move(condition), 1));
    }
    block->pushBack(std::unique_ptr<Statement>(new Jump(
        std::move(condition), JumpTarget(caseTarget),
        JumpTarget(missTarget))));
    return selectorRead;
}

void recordDispatchDataflow(
        dflow::Dataflow &dataflow, const DispatchTerms &terms,
        Term *selectorDefinition,
        const MemoryLocation &selectorLocation,
        const MemoryLocation &temporaryLocation,
        const MemoryLocation &flagLocation) {
    dataflow.setMemoryLocation(terms.selectorRead, selectorLocation);
    dataflow.setMemoryLocation(
        terms.temporaryDefinition, temporaryLocation);
    dataflow.setMemoryLocation(terms.temporaryRead, temporaryLocation);
    dataflow.setMemoryLocation(terms.flagDefinition, flagLocation);
    dataflow.setMemoryLocation(terms.flagRead, flagLocation);
    dataflow.getDefinitions(terms.selectorRead).addDefinition(
        selectorLocation, selectorDefinition);
    dataflow.getDefinitions(terms.temporaryRead).addDefinition(
        temporaryLocation, terms.temporaryDefinition);
    dataflow.getDefinitions(terms.flagRead).addDefinition(
        flagLocation, terms.flagDefinition);
}

void addRepeatedStackFlagComputation(
        BasicBlock *block, const Statement *after,
        const MemoryLocation &selectorLocation,
        const MemoryLocation &flagLocation, Term *selectorDefinition,
        dflow::Dataflow &dataflow) {
    std::unique_ptr<Term> selector =
        locationAccess(selectorLocation, true);
    Term *selectorRead = selector.get();
    std::unique_ptr<Term> comparison(new BinaryOperator(
        BinaryOperator::UNSIGNED_LESS, std::move(selector),
        constant(32, 0x200), 1));
    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(flagLocation));
    Term *flagDefinition = destination.get();
    block->insertAfter(after, std::unique_ptr<Statement>(new Assignment(
        std::move(destination), std::move(comparison))));

    dataflow.setMemoryLocation(selectorRead, selectorLocation);
    dataflow.getDefinitions(selectorRead).addDefinition(
        selectorLocation, selectorDefinition);
    dataflow.setMemoryLocation(flagDefinition, flagLocation);
}

Term *addUnknownFlagComputation(
        BasicBlock *block, const Statement *after,
        const MemoryLocation &flagLocation,
        dflow::Dataflow &dataflow) {
    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(flagLocation));
    Term *flagDefinition = destination.get();
    block->insertAfter(after, std::unique_ptr<Statement>(new Assignment(
        std::move(destination), std::unique_ptr<Term>(
            new Intrinsic(Intrinsic::UNKNOWN, 1)))));
    dataflow.setMemoryLocation(flagDefinition, flagLocation);
    return flagDefinition;
}

const cflow::Switch *analyzeSwitch(
        Function &function, dflow::Dataflow &dataflow,
        cflow::Graph &graph) {
    dataflow.setConverged(true);
    CFG cfg(function.basicBlocks());
    CancellationToken canceled;
    Dominators dominators(cfg, canceled, function.entry());
    PostDominators postdominators(cfg, canceled);
    dflow::DefUseGraph defUse(dataflow);
    dflow::ValueProvenance provenance(
        dataflow, defUse, dominators, cfg);
    dflow::ExpressionIdentity identity(
        dataflow, defUse, provenance);

    cflow::GraphBuilder()(graph, &function);
    cflow::StructureAnalyzer(
        graph, dataflow, defUse, provenance, identity,
        postdominators).analyze();

    foreach (const cflow::Node *node, graph.nodes()) {
        const cflow::Region *region = node->as<cflow::Region>();
        if (region) {
            const cflow::Switch *witch = region->as<cflow::Switch>();
            if (witch && witch->isComparisonChain()) {
                return witch;
            }
        }
    }
    return nullptr;
}

class TwoCaseFixture {
public:
    MemoryLocation selector;
    MemoryLocation temporary;
    MemoryLocation flag;
    Function function;
    dflow::Dataflow dataflow;
    BasicBlock *first;
    BasicBlock *second;
    BasicBlock *firstCase;
    BasicBlock *secondCase;
    BasicBlock *defaultCase;
    BasicBlock *merge;
    Term *selectorDefinition;
    DispatchTerms firstDispatch;
    DispatchTerms secondDispatch;

    TwoCaseFixture(ConstantValue firstValue,
                   ConstantValue secondValue,
                   bool secondNotEqual,
                   bool fallthrough,
                   Domain domainBase,
                   bool dereferenceSelector = false,
                   Domain selectorDomain = MemoryDomain::UNKNOWN):
        selector(selectorDomain == MemoryDomain::UNKNOWN ?
                     domainBase : selectorDomain,
                 dereferenceSelector ? 64 : 0, 32),
        temporary(domainBase + (dereferenceSelector ? 0 : 1), 0, 32),
        flag(domainBase + (dereferenceSelector ? 1 : 2), 0, 1),
        first(addBlock(function)),
        second(addBlock(function)),
        firstCase(addBlock(function)),
        secondCase(addBlock(function)),
        defaultCase(addBlock(function)),
        merge(addBlock(function)),
        selectorDefinition(nullptr)
    {
        function.setEntry(first);
        selectorDefinition = addDefinition(
            first, selector, std::unique_ptr<Term>(
                new Intrinsic(Intrinsic::UNKNOWN, 32)),
            dereferenceSelector);
        firstDispatch = addCmpDispatch(
            first, firstCase, second, firstValue, selector,
            temporary, flag, false, dereferenceSelector);
        if (secondNotEqual) {
            secondDispatch = addCmpDispatch(
                second, defaultCase, secondCase, secondValue,
                selector, temporary, flag, true,
                dereferenceSelector);
        } else {
            secondDispatch = addCmpDispatch(
                second, secondCase, defaultCase, secondValue,
                selector, temporary, flag, false,
                dereferenceSelector);
        }

        firstCase->pushBack(std::unique_ptr<Statement>(new Jump(
            JumpTarget(fallthrough ? secondCase : merge))));
        secondCase->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(merge))));
        defaultCase->pushBack(std::unique_ptr<Statement>(
            new Jump(JumpTarget(merge))));
        merge->pushBack(std::unique_ptr<Statement>(new Halt()));

        dataflow.setMemoryLocation(selectorDefinition, selector);
        recordDispatchDataflow(
            dataflow, firstDispatch, selectorDefinition,
            selector, temporary, flag);
        recordDispatchDataflow(
            dataflow, secondDispatch, selectorDefinition,
            selector, temporary, flag);
    }

    const cflow::Switch *analyze(cflow::Graph &graph) {
        return analyzeSwitch(function, dataflow, graph);
    }
};

void testCmpChainAndFallthrough() {
    TwoCaseFixture fixture(
        0x10, 0x20, true, true,
        MemoryDomain::FIRST_REGISTER);

    cflow::Graph graph;
    const cflow::Switch *witch = fixture.analyze(graph);
    check(witch != nullptr,
          "a proved CMP/Jcc chain must become a comparison switch");
    check(witch->dispatchNodes().size() == 2 &&
              witch->cases().size() == 2,
          "the switch must retain every consumed comparison");
    check(witch->cases()[0].value() == 0x10 &&
              witch->cases()[0].basicBlock() == fixture.firstCase &&
              witch->cases()[1].value() == 0x20 &&
              witch->cases()[1].basicBlock() == fixture.secondCase,
          "case values and equality destinations must be exact");
    check(witch->defaultBasicBlock() == fixture.defaultCase,
          "JNZ orientation must preserve the miss/default destination");
    check(witch->exitBasicBlock() == fixture.merge,
          "all branches must use their proved common merge");
    check(witch->dispatchNodes().front()->basicBlock() == fixture.first,
          "the always-executed first prelude must remain identifiable");
}

void testDirectEqualityChain() {
    const MemoryLocation selector(
        MemoryDomain::FIRST_REGISTER + 5, 0, 32);
    Function function;
    dflow::Dataflow dataflow;
    BasicBlock *first = addBlock(function);
    BasicBlock *second = addBlock(function);
    BasicBlock *firstCase = addBlock(function);
    BasicBlock *secondCase = addBlock(function);
    BasicBlock *defaultCase = addBlock(function);
    BasicBlock *merge = addBlock(function);
    function.setEntry(first);

    Term *definition = addDefinition(
        first, selector, std::unique_ptr<Term>(
            new Intrinsic(Intrinsic::UNKNOWN, 32)));
    Term *firstRead = addDirectEqualityDispatch(
        first, firstCase, second, 3, selector);
    Term *secondRead = addDirectEqualityDispatch(
        second, defaultCase, secondCase, 4, selector, true);
    firstCase->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(merge))));
    secondCase->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(merge))));
    defaultCase->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(merge))));
    merge->pushBack(std::unique_ptr<Statement>(new Halt()));

    dataflow.setMemoryLocation(definition, selector);
    dataflow.setMemoryLocation(firstRead, selector);
    dataflow.setMemoryLocation(secondRead, selector);
    dataflow.getDefinitions(firstRead).addDefinition(
        selector, definition);
    dataflow.getDefinitions(secondRead).addDefinition(
        selector, definition);

    cflow::Graph graph;
    const cflow::Switch *witch =
        analyzeSwitch(function, dataflow, graph);
    check(witch != nullptr && witch->cases().size() == 2,
          "direct equality and inequality tests must also form a switch");
}

void testResolvedStackSelector() {
    TwoCaseFixture fixture(
        0x110, 0x111, false, false,
        MemoryDomain::FIRST_REGISTER + 70, true,
        MemoryDomain::STACK);
    const MemoryLocation firstSiblingFlag(
        MemoryDomain::FIRST_REGISTER + 72, 0, 1);
    const MemoryLocation secondSiblingFlag(
        MemoryDomain::FIRST_REGISTER + 73, 0, 1);
    const MemoryLocation firstUnknownFlag(
        MemoryDomain::FIRST_REGISTER + 74, 0, 1);
    const MemoryLocation secondUnknownFlag(
        MemoryDomain::FIRST_REGISTER + 75, 0, 1);
    addRepeatedStackFlagComputation(
        fixture.first,
        fixture.firstDispatch.selectorRead->statement(),
        fixture.selector, firstSiblingFlag,
        fixture.selectorDefinition, fixture.dataflow);
    addRepeatedStackFlagComputation(
        fixture.second,
        fixture.secondDispatch.selectorRead->statement(),
        fixture.selector, secondSiblingFlag,
        fixture.selectorDefinition, fixture.dataflow);
    addUnknownFlagComputation(
        fixture.first,
        fixture.firstDispatch.selectorRead->statement(),
        firstUnknownFlag, fixture.dataflow);
    addUnknownFlagComputation(
        fixture.second,
        fixture.secondDispatch.selectorRead->statement(),
        secondUnknownFlag, fixture.dataflow);

    cflow::Graph graph;
    const cflow::Switch *witch = fixture.analyze(graph);
    check(witch != nullptr && witch->cases().size() == 2,
          "a resolved stack argument with one exact definition must be "
          "eligible as a switch selector");
}

void testGlobalDereferenceSelectorRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 80, true,
        MemoryDomain::MEMORY);

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "an externally mutable memory selector must remain an if chain");
}

void testDuplicateCaseRejected() {
    TwoCaseFixture fixture(
        7, 7, false, false,
        MemoryDomain::FIRST_REGISTER + 10);
    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "duplicate case values must reject the whole rewrite");
}

void testSelectorRedefinitionRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 20);
    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(fixture.selector));
    Term *redefinition = destination.get();
    fixture.second->pushFront(std::unique_ptr<Statement>(new Assignment(
        std::move(destination), std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::UNKNOWN, 32)))));
    fixture.dataflow.setMemoryLocation(redefinition, fixture.selector);
    dflow::ReachingDefinitions &definitions =
        fixture.dataflow.getDefinitions(
            fixture.secondDispatch.selectorRead);
    definitions.clear();
    definitions.addDefinition(fixture.selector, redefinition);

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "a selector redefinition between tests must reject the rewrite");
}

void testLaterCallRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 30);
    fixture.second->pushFront(std::unique_ptr<Statement>(
        new Call(constant(32, 0x1000))));

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "an opaque call in a later dispatch prelude must be preserved");
}

void testAnalysisCallbackDoesNotBlockRewrite() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 35);
    fixture.second->pushFront(std::unique_ptr<Statement>(
        new Callback([]() {})));

    cflow::Graph graph;
    check(fixture.analyze(graph) != nullptr,
          "dataflow-only callback instrumentation must not look like a "
          "runtime side effect");
}

void testObservableLaterReadRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 40);
    const MemoryLocation scratch(
        MemoryDomain::FIRST_REGISTER + 43, 0, 32);
    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(scratch));
    Term *definition = destination.get();
    fixture.second->pushFront(std::unique_ptr<Statement>(new Assignment(
        std::move(destination), std::unique_ptr<Term>(new Dereference(
            constant(32, 0x2000), MemoryDomain::MEMORY, 32)))));
    fixture.dataflow.setMemoryLocation(definition, scratch);

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "a trapping or observable later read must reject the rewrite");
}

void testLaterMemoryWriteRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 90, true,
        MemoryDomain::STACK);
    std::unique_ptr<Term> destination(new Dereference(
        constant(32, 0x1000), MemoryDomain::MEMORY, 32));
    Term *write = destination.get();
    fixture.second->pushFront(std::unique_ptr<Statement>(new Assignment(
        std::move(destination), constant(32, 7))));
    fixture.dataflow.setMemoryLocation(write, fixture.selector);

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "a memory write on the comparison miss path must be preserved");
}

void testFirstPostSelectorCallRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 100);
    fixture.first->insertAfter(
        fixture.firstDispatch.selectorRead->statement(),
        std::unique_ptr<Statement>(new Call(constant(32, 0x1000))));

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "selector evaluation must not move across an observable call");
}

void testUsedNonrepeatableFlagRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 110);
    const MemoryLocation unknownFlag(
        MemoryDomain::FIRST_REGISTER + 113, 0, 1);
    const MemoryLocation sink(
        MemoryDomain::FIRST_REGISTER + 114, 0, 1);
    Term *flagDefinition = addUnknownFlagComputation(
        fixture.first,
        fixture.firstDispatch.selectorRead->statement(),
        unknownFlag, fixture.dataflow);

    std::unique_ptr<Term> flagReadStorage(
        new MemoryLocationAccess(unknownFlag));
    Term *flagRead = flagReadStorage.get();
    std::unique_ptr<Term> destination(
        new MemoryLocationAccess(sink));
    Term *sinkDefinition = destination.get();
    fixture.firstCase->insertBefore(
        fixture.firstCase->getJump(),
        std::unique_ptr<Statement>(new Assignment(
            std::move(destination), std::move(flagReadStorage))));
    fixture.dataflow.setMemoryLocation(flagRead, unknownFlag);
    fixture.dataflow.setMemoryLocation(sinkDefinition, sink);
    fixture.dataflow.getDefinitions(flagRead).addDefinition(
        unknownFlag, flagDefinition);

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "a used nonrepeatable flag must not move across selector evaluation");
}

void testExternalCaseEntryRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 50);
    BasicBlock *external = addBlock(fixture.function);
    external->pushBack(std::unique_ptr<Statement>(
        new Jump(JumpTarget(fixture.firstCase))));

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "a case body with an external entry must reject the region");
}

void testMissingCommonMergeRejected() {
    TwoCaseFixture fixture(
        1, 2, false, false,
        MemoryDomain::FIRST_REGISTER + 60);
    fixture.firstCase->erase(fixture.firstCase->getJump());
    fixture.firstCase->pushBack(
        std::unique_ptr<Statement>(new Halt()));

    cflow::Graph graph;
    check(fixture.analyze(graph) == nullptr,
          "branches without a real common merge must remain an if chain");
}

void testArrayAccessScaleGuards() {
    const auto recognizeShift = [](ConstantValue shift) {
        dflow::Dataflow dataflow;

        std::unique_ptr<Term> base = constant(32, 0x1000);
        Term *baseTerm = base.get();
        std::unique_ptr<Term> amount = constant(32, shift);
        Term *amountTerm = amount.get();
        std::unique_ptr<Term> scaled(new BinaryOperator(
            BinaryOperator::SHL,
            std::unique_ptr<Term>(new Intrinsic(
                Intrinsic::UNKNOWN, 32)),
            std::move(amount), 32));
        std::unique_ptr<Term> address(new BinaryOperator(
            BinaryOperator::ADD, std::move(base),
            std::move(scaled), 32));
        std::unique_ptr<Statement> access(new Touch(
            std::unique_ptr<Term>(new Dereference(
                std::move(address), MemoryDomain::MEMORY, 32)),
            Term::READ));

        dataflow.getValue(baseTerm)->setAbstractValue(
            dflow::AbstractValue(SizedValue(32, 0x1000)));
        dataflow.getValue(amountTerm)->setAbstractValue(
            dflow::AbstractValue(SizedValue(32, shift)));
        dataflow.setConverged(true);
        const misc::ArrayAccess result =
            misc::recognizeArrayAccess(
                access->asTouch()->term(), dataflow);
        return result ? result.stride() : ConstantValue(0);
    };

    check(recognizeShift(31) == (ConstantValue(1) << 31),
          "a representable shift scale must be recognized exactly");
    check(recognizeShift(32) == 0,
          "a shift outside the IR result width must not become a host-width "
          "array scale");

    dflow::Dataflow dataflow;
    std::unique_ptr<Term> base = constant(32, 0x1000);
    Term *baseTerm = base.get();
    std::unique_ptr<Term> zero = constant(32, 0);
    Term *zeroTerm = zero.get();
    std::unique_ptr<Term> scaled(new BinaryOperator(
        BinaryOperator::MUL, std::move(zero),
        std::unique_ptr<Term>(new Intrinsic(
            Intrinsic::UNKNOWN, 32)), 32));
    std::unique_ptr<Term> address(new BinaryOperator(
        BinaryOperator::ADD, std::move(base), std::move(scaled), 32));
    std::unique_ptr<Statement> access(new Touch(
        std::unique_ptr<Term>(new Dereference(
            std::move(address), MemoryDomain::MEMORY, 32)),
        Term::READ));
    dataflow.getValue(baseTerm)->setAbstractValue(
        dflow::AbstractValue(SizedValue(32, 0x1000)));
    dataflow.getValue(zeroTerm)->setAbstractValue(
        dflow::AbstractValue(SizedValue(32, 0)));
    dataflow.setConverged(true);
    check(!misc::recognizeArrayAccess(
              access->asTouch()->term(), dataflow),
          "a zero multiplier is not an indexing operation");
}

} // anonymous namespace

int main() {
    try {
        testCmpChainAndFallthrough();
        testDirectEqualityChain();
        testResolvedStackSelector();
        testGlobalDereferenceSelectorRejected();
        testDuplicateCaseRejected();
        testSelectorRedefinitionRejected();
        testLaterCallRejected();
        testAnalysisCallbackDoesNotBlockRewrite();
        testObservableLaterReadRejected();
        testLaterMemoryWriteRejected();
        testFirstPostSelectorCallRejected();
        testUsedNonrepeatableFlagRejected();
        testExternalCaseEntryRejected();
        testMissingCommonMergeRejected();
        testArrayAccessScaleGuards();
    } catch (const std::exception &exception) {
        std::cerr << "comparison-switch regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }
    return 0;
}

/* vim:set et sts=4 sw=4: */
