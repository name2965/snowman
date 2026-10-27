/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <cstdio>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

#include <QLatin1String>
#include <QString>

#include <nc/core/ir/calling/FunctionPrototype.h>
#include <nc/core/ir/calling/SymbolPrototypeRegistry.h>

using namespace nc;
using namespace nc::core::ir::calling;

namespace {

void check(bool condition, const char *message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

QString text(const char *value) {
    return QString(QLatin1String(value));
}

TypeDescription integerType(SmallBitSize size, const char *name) {
    return TypeDescription(
        TypeDescription::INTEGER, size, false, text(name));
}

TypeDescription pointerType(SmallBitSize size, const char *name) {
    return TypeDescription(
        TypeDescription::POINTER, size, true, text(name));
}

std::shared_ptr<const FunctionPrototype> makeCallbackPrototype(
        bool memoryEffectsAreComplete, SmallBitSize resultSize = 32,
        const char *abiConventionName = "callback_abi",
        bool variadic = false) {
    std::vector<ParameterDescription> parameters;
    parameters.push_back(ParameterDescription(
        text("context"), pointerType(64, "context_pointer"),
        ParameterDescription::PointeeAccess::READ));

    return std::make_shared<const FunctionPrototype>(
        integerType(resultSize, resultSize == 32 ?
            "callback_result" : "wide_callback_result"),
        std::move(parameters), text("callback_convention"),
        text("callback_contract"), memoryEffectsAreComplete,
        text(abiConventionName), variadic);
}

std::shared_ptr<const FunctionPrototype> makeParentPrototype(
        bool memoryEffectsAreComplete,
        std::shared_ptr<const FunctionPrototype> callback) {
    std::vector<ParameterDescription> parameters;
    parameters.push_back(ParameterDescription(
        text("state"), pointerType(64, "state_pointer"),
        ParameterDescription::PointeeAccess::READ_WRITE));
    parameters.push_back(ParameterDescription(
        text("operation"), pointerType(64, "operation_pointer"),
        ParameterDescription::PointeeAccess::NONE, std::move(callback)));

    return std::make_shared<const FunctionPrototype>(
        integerType(32, "operation_result"), std::move(parameters),
        text("parent_convention"), text("process_record"),
        memoryEffectsAreComplete);
}

std::shared_ptr<const FunctionPrototype> makeSharedCallbackDag(
        unsigned int depth, std::size_t fanout, SmallBitSize pointerSize) {
    const TypeDescription voidType(TypeDescription::VOID, 0, false);
    std::shared_ptr<const FunctionPrototype> child =
        std::make_shared<const FunctionPrototype>(
            voidType, std::vector<ParameterDescription>(), QString(),
            QString(), true, text("cdecl32"));

    for (unsigned int level = 0; level < depth; ++level) {
        std::vector<ParameterDescription> parameters;
        parameters.reserve(fanout);
        for (std::size_t index = 0; index < fanout; ++index) {
            parameters.push_back(ParameterDescription(
                text("callback"),
                pointerType(pointerSize, "callback_pointer"),
                ParameterDescription::PointeeAccess::NONE, child));
        }
        child = std::make_shared<const FunctionPrototype>(
            voidType, std::move(parameters), QString(), QString(), true,
            text("cdecl32"));
    }
    return child;
}

struct PrototypePairFixture {
    std::shared_ptr<const FunctionPrototype> left;
    std::shared_ptr<const FunctionPrototype> right;
};

std::shared_ptr<const FunctionPrototype> makeScalarLeafPrototype(
        std::size_t parameterCount) {
    const TypeDescription voidType(TypeDescription::VOID, 0, false);
    std::vector<ParameterDescription> parameters;
    parameters.reserve(parameterCount);
    for (std::size_t index = 0; index < parameterCount; ++index) {
        parameters.push_back(ParameterDescription(
            text("value"), integerType(32, "value_type"),
            ParameterDescription::PointeeAccess::NONE));
    }
    return std::make_shared<const FunctionPrototype>(
        voidType, std::move(parameters), QString(), QString(), true,
        text("cdecl32"));
}

std::shared_ptr<const FunctionPrototype> makeCallbackWrapper(
        const std::shared_ptr<const FunctionPrototype> &callback) {
    const TypeDescription voidType(TypeDescription::VOID, 0, false);
    std::vector<ParameterDescription> parameters;
    parameters.push_back(ParameterDescription(
        text("callback"), pointerType(32, "callback_pointer"),
        ParameterDescription::PointeeAccess::NONE, callback));
    return std::make_shared<const FunctionPrototype>(
        voidType, std::move(parameters), QString(), QString(), true,
        text("cdecl32"));
}

QString indexedName(const char *prefix, std::size_t index) {
    char name[64];
    const int length = std::snprintf(
        name, sizeof(name), "%s%lu", prefix,
        static_cast<unsigned long>(index));
    check(length > 0 && static_cast<std::size_t>(length) < sizeof(name),
          "could not format a unique provider-record name");
    return text(name);
}

PrototypePairFixture makeAdversarialCallbackPairExpansion(
        std::size_t width, std::size_t leafParameterCount) {
    const TypeDescription voidType(TypeDescription::VOID, 0, false);
    std::vector<std::shared_ptr<const FunctionPrototype>> leftLeaves;
    std::vector<std::shared_ptr<const FunctionPrototype>> rightLeaves;
    leftLeaves.reserve(width);
    rightLeaves.reserve(width);
    for (std::size_t index = 0; index < width; ++index) {
        leftLeaves.push_back(
            makeScalarLeafPrototype(leafParameterCount));
        rightLeaves.push_back(
            makeScalarLeafPrototype(leafParameterCount));
    }

    std::vector<std::shared_ptr<const FunctionPrototype>> leftMiddle;
    std::vector<std::shared_ptr<const FunctionPrototype>> rightMiddle;
    leftMiddle.reserve(width);
    rightMiddle.reserve(width);
    for (std::size_t row = 0; row < width; ++row) {
        std::vector<ParameterDescription> leftParameters;
        std::vector<ParameterDescription> rightParameters;
        leftParameters.reserve(width);
        rightParameters.reserve(width);
        for (std::size_t column = 0; column < width; ++column) {
            leftParameters.push_back(ParameterDescription(
                text("callback"),
                pointerType(32, "callback_pointer"),
                ParameterDescription::PointeeAccess::NONE,
                leftLeaves[row]));
            rightParameters.push_back(ParameterDescription(
                text("callback"),
                pointerType(32, "callback_pointer"),
                ParameterDescription::PointeeAccess::NONE,
                rightLeaves[column]));
        }
        leftMiddle.push_back(std::make_shared<const FunctionPrototype>(
            voidType, std::move(leftParameters), QString(), QString(), true,
            text("cdecl32")));
        rightMiddle.push_back(std::make_shared<const FunctionPrototype>(
            voidType, std::move(rightParameters), QString(), QString(), true,
            text("cdecl32")));
    }

    std::vector<ParameterDescription> leftRootParameters;
    std::vector<ParameterDescription> rightRootParameters;
    leftRootParameters.reserve(width);
    rightRootParameters.reserve(width);
    for (std::size_t index = 0; index < width; ++index) {
        leftRootParameters.push_back(ParameterDescription(
            text("callback"), pointerType(32, "callback_pointer"),
            ParameterDescription::PointeeAccess::NONE,
            leftMiddle[index]));
        rightRootParameters.push_back(ParameterDescription(
            text("callback"), pointerType(32, "callback_pointer"),
            ParameterDescription::PointeeAccess::NONE,
            rightMiddle[index]));
    }

    PrototypePairFixture result;
    result.left = std::make_shared<const FunctionPrototype>(
        voidType, std::move(leftRootParameters), QString(), QString(), true,
        text("cdecl32"));
    result.right = std::make_shared<const FunctionPrototype>(
        voidType, std::move(rightRootParameters), QString(), QString(), true,
        text("cdecl32"));
    return result;
}

SymbolPrototypeRecord makeRecord(
        const char *conventionName,
        std::shared_ptr<const FunctionPrototype> prototype,
        ByteSize stackArgumentsSize = 16,
        bool doesNotReturn = false) {
    return SymbolPrototypeRecord(
        std::move(prototype), text(conventionName),
        boost::optional<ByteSize>(stackArgumentsSize), doesNotReturn);
}

class RecordingProvider: public SymbolPrototypeProvider {
    QString id_;
    int priority_;
    std::vector<NamedSymbolPrototype> prototypes_;
    mutable bool queried_;
    mutable QString architecture_;
    mutable QString operatingSystem_;
    mutable SmallBitSize bitness_;

public:
    RecordingProvider(QString id, int priority,
                      std::vector<NamedSymbolPrototype> prototypes):
        id_(std::move(id)), priority_(priority),
        prototypes_(std::move(prototypes)), queried_(false), bitness_(0)
    {}

    QString id() const override { return id_; }
    int priority() const override { return priority_; }

    std::vector<NamedSymbolPrototype> getPrototypes(
            const SymbolPrototypeTarget &target) const override {
        queried_ = true;
        architecture_ = target.architecture();
        operatingSystem_ = target.operatingSystem();
        bitness_ = target.bitness();
        return prototypes_;
    }

    bool queried() const { return queried_; }
    const QString &architecture() const { return architecture_; }
    const QString &operatingSystem() const { return operatingSystem_; }
    SmallBitSize bitness() const { return bitness_; }
};

void testProviderReceivesTargetAndPopulatesRegistry() {
    const auto prototype = makeParentPrototype(
        true, makeCallbackPrototype(true));

    std::vector<NamedSymbolPrototype> prototypes;
    prototypes.push_back(NamedSymbolPrototype(
        text("runtime.alpha"), text("transform_record"),
        makeRecord("qualified_convention", prototype)));
    prototypes.push_back(NamedSymbolPrototype(
        text("runtime.beta"), text("transform_record"),
        makeRecord("second_module_convention", prototype)));
    prototypes.push_back(NamedSymbolPrototype(
        text("transform_record"),
        makeRecord("fallback_convention", prototype)));

    RecordingProvider provider(
        text("target-recording-provider"), 40, std::move(prototypes));
    SymbolPrototypeRegistry registry;
    registry.addProvider(provider, SymbolPrototypeTarget(
        text("synthetic-architecture"), text("research-os"), 64));

    check(provider.queried(),
          "the registry must query each prototype provider");
    check(provider.architecture() == text("synthetic-architecture"),
          "the provider must receive the target architecture");
    check(provider.operatingSystem() == text("research-os"),
          "the provider must receive the target operating system");
    check(provider.bitness() == 64,
          "the provider must receive the target bitness");

    const SymbolPrototypeRecord *qualified = registry.lookup(
        text("runtime.alpha"), text("transform_record"));
    check(qualified != nullptr &&
              qualified->conventionName() == text("qualified_convention"),
          "a provider's module-qualified record must be registered");

    const SymbolPrototypeRecord *secondModule = registry.lookup(
        text("runtime.beta"), text("transform_record"));
    check(secondModule != nullptr &&
              secondModule->conventionName() ==
                  text("second_module_convention"),
          "equal leaf names from different modules must remain distinct");

    const SymbolPrototypeRecord *fallback =
        registry.lookup(text("transform_record"));
    check(fallback != nullptr &&
              fallback->conventionName() == text("fallback_convention"),
          "an explicitly unqualified provider record must remain available");

    check(registry.lookup(
              text("runtime.gamma"), text("transform_record")) == nullptr,
          "qualified lookup must not borrow another module's record or fallback");
    check(registry.lookup(QString(), text("transform_record")) == nullptr,
          "qualified lookup must reject an empty module instead of falling back");
}

void testProgrammaticProviderCannotBypassTargetLayout() {
    const TypeDescription voidType(
        TypeDescription::VOID, 0, false);

    std::vector<ParameterDescription> validParameters;
    validParameters.push_back(ParameterDescription(
        text("value"), integerType(32, "value_type"),
        ParameterDescription::PointeeAccess::NONE));
    const auto validPrototype = std::make_shared<const FunctionPrototype>(
        voidType, std::move(validParameters));

    std::vector<ParameterDescription> wideParameters;
    wideParameters.push_back(ParameterDescription(
        text("wide"), integerType(64, "wide_type"),
        ParameterDescription::PointeeAccess::NONE));
    const auto widePrototype = std::make_shared<const FunctionPrototype>(
        voidType, std::move(wideParameters));

    const auto invalidCallback = std::make_shared<const FunctionPrototype>(
        integerType(64, "wide_callback_result"),
        std::vector<ParameterDescription>(), QString(), QString(), false,
        text("cdecl32"));
    std::vector<ParameterDescription> callbackParameters;
    callbackParameters.push_back(ParameterDescription(
        text("callback"), pointerType(32, "callback_pointer"),
        ParameterDescription::PointeeAccess::NONE, invalidCallback));
    const auto invalidCallbackParent =
        std::make_shared<const FunctionPrototype>(
            voidType, std::move(callbackParameters));

    std::vector<NamedSymbolPrototype> records;
    records.push_back(NamedSymbolPrototype(
        text("runtime.layout"), text("valid"),
        makeRecord("cdecl32", validPrototype, 4)));
    records.push_back(NamedSymbolPrototype(
        text("runtime.layout"), text("wide"),
        makeRecord("cdecl32", widePrototype, 4)));
    records.push_back(NamedSymbolPrototype(
        text("runtime.layout"), text("nested_wide"),
        makeRecord("cdecl32", invalidCallbackParent, 4)));

    RecordingProvider provider(
        text("programmatic-layout-provider"), 10, std::move(records));
    SymbolPrototypeRegistry registry;
    registry.addProvider(provider, SymbolPrototypeTarget(
        text("x86"), text("windows"), 32));

    check(registry.lookup(text("runtime.layout"), text("valid")) != nullptr,
          "a target-compatible programmatic record was rejected");
    check(registry.lookup(text("runtime.layout"), text("wide")) == nullptr,
          "a multi-slot scalar bypassed provider target validation");
    check(registry.lookup(
              text("runtime.layout"), text("nested_wide")) == nullptr,
          "an incompatible nested callback bypassed target validation");
}

void testSharedCallbackDagValidationIsBounded() {
    /* This is 17 allocated prototypes, not an 8^16 tree. Validation must
     * preserve that graph sharing instead of recursively revisiting the same
     * child once per incoming parameter edge. */
    const auto prototype = makeSharedCallbackDag(16, 8, 32);
    check(isFunctionPrototypeTargetCompatible(*prototype, 32),
          "a target-compatible shared callback DAG was rejected");

    std::vector<NamedSymbolPrototype> records;
    records.push_back(NamedSymbolPrototype(
        text("runtime.dag"), text("shared_callbacks"),
        makeRecord("cdecl32", prototype, 32)));
    RecordingProvider provider(
        text("shared-dag-provider"), 10, std::move(records));
    SymbolPrototypeRegistry registry;
    registry.addProvider(provider, SymbolPrototypeTarget(
        text("x86"), text("windows"), 32));

    check(registry.lookup(
              text("runtime.dag"), text("shared_callbacks")) != nullptr,
          "provider ingestion lost a valid shared callback DAG");
}

void testSharedCallbackDagEquivalenceIsBounded() {
    const auto left = makeSharedCallbackDag(16, 8, 32);
    const auto right = makeSharedCallbackDag(16, 8, 32);
    check(areFunctionPrototypesEquivalent(*left, *right),
          "distinct structurally equal shared callback DAGs were rejected");
}

void testCallbackChainBeyondDepthLimitFailsClosed() {
    const auto left = makeSharedCallbackDag(17, 1, 32);
    const auto right = makeSharedCallbackDag(17, 1, 32);
    check(!areFunctionPrototypesEquivalent(*left, *right),
          "separately allocated callback chains bypassed the depth limit");
}

void testAdversarialPrototypePairExpansionFailsClosed() {
    {
        /* The middle layer expands 256 aligned pairs into 256^2 distinct
         * leaf pairs while each input graph contains only 513 prototypes.
         * Equality must stop at its pair budget instead of traversing an
         * attacker-controlled Cartesian product without a bound. */
        const PrototypePairFixture pair =
            makeAdversarialCallbackPairExpansion(256, 0);
        check(!areFunctionPrototypesEquivalent(
                  *pair.left, *pair.right),
              "prototype-pair expansion exceeded its budget without failing closed");
    }

    {
        /* Five scalar fields on each of 224^2 leaf pairs exhaust the
         * parameter-comparison budget before the pair budget. */
        const PrototypePairFixture pair =
            makeAdversarialCallbackPairExpansion(224, 5);
        check(!areFunctionPrototypesEquivalent(
                  *pair.left, *pair.right),
              "parameter comparison expansion exceeded its budget without failing closed");
    }
}

void testProviderAcceptsManyShallowRecords() {
    const QString module = text("runtime.bulk");
    const auto prototype = std::make_shared<const FunctionPrototype>(
        integerType(32, "result"),
        std::vector<ParameterDescription>(), QString(), QString(), true,
        text("cdecl32"));
    std::vector<NamedSymbolPrototype> records;
    records.reserve(5000);
    for (std::size_t index = 0; index < 5000; ++index) {
        char name[32];
        const int length = std::snprintf(
            name, sizeof(name), "function_%lu",
            static_cast<unsigned long>(index));
        check(length > 0 &&
                  static_cast<std::size_t>(length) < sizeof(name),
              "could not format a unique shallow-record name");
        records.push_back(NamedSymbolPrototype(
            module, text(name),
            makeRecord("cdecl32", prototype, 0)));
    }

    RecordingProvider provider(
        text("large-shallow-provider"), 10, std::move(records));
    SymbolPrototypeRegistry registry;
    registry.addProvider(provider, SymbolPrototypeTarget(
        text("x86"), text("windows"), 32));

    check(registry.lookup(module, text("function_0")) != nullptr,
          "a large provider lost its first valid shallow record");
    check(registry.lookup(module, text("function_2500")) != nullptr,
          "a large provider lost a middle valid shallow record");
    check(registry.lookup(module, text("function_4999")) != nullptr,
          "a large provider lost its last valid shallow record");
}

void testProviderBudgetsAreRecountedForEveryRecord() {
    const QString module = text("runtime.per_record_budget");
    const TypeDescription voidType(TypeDescription::VOID, 0, false);

    {
        /* Prevalidate each four-node subgraph at the same callback depth at
         * which a later root will encounter it. A provider-wide compatibility
         * cache must not let that root combine 4096 cached descendants plus
         * itself past the per-record unique-prototype budget. */
        std::vector<NamedSymbolPrototype> records;
        std::vector<std::shared_ptr<const FunctionPrototype>> subgraphs;
        subgraphs.reserve(1024);
        records.reserve(1025);
        for (std::size_t index = 0; index < 1024; ++index) {
            const auto subgraph = makeSharedCallbackDag(3, 1, 32);
            subgraphs.push_back(subgraph);
            records.push_back(NamedSymbolPrototype(
                module, indexedName("unique_warmup_", index),
                makeRecord(
                    "cdecl32", makeCallbackWrapper(subgraph), 0)));
        }

        std::vector<ParameterDescription> combinedParameters;
        combinedParameters.reserve(subgraphs.size());
        for (const auto &subgraph : subgraphs) {
            combinedParameters.push_back(ParameterDescription(
                text("callback"), pointerType(32, "callback_pointer"),
                ParameterDescription::PointeeAccess::NONE, subgraph));
        }
        const auto combined = std::make_shared<const FunctionPrototype>(
            voidType, std::move(combinedParameters), QString(), QString(),
            true, text("cdecl32"));
        records.push_back(NamedSymbolPrototype(
            module, text("unique_combined"),
            makeRecord("cdecl32", combined, 0)));

        RecordingProvider provider(
            text("unique-budget-provider"), 10, std::move(records));
        SymbolPrototypeRegistry registry;
        registry.addProvider(provider, SymbolPrototypeTarget(
            text("x86"), text("windows"), 32));

        check(registry.lookup(module, text("unique_warmup_0")) != nullptr &&
                  registry.lookup(
                      module, text("unique_warmup_1023")) != nullptr,
              "individually valid unique-budget warmup records were rejected");
        check(registry.lookup(module, text("unique_combined")) == nullptr,
              "cached subgraphs bypassed the per-record unique-prototype budget");
    }

    {
        /* Likewise, 65 individually valid 1024-parameter callbacks exceed
         * 65,536 parameter visits only when one later record combines them.
         * Cached true results must not erase that later record's footprint. */
        std::vector<NamedSymbolPrototype> records;
        std::vector<std::shared_ptr<const FunctionPrototype>> subgraphs;
        subgraphs.reserve(65);
        records.reserve(66);
        for (std::size_t index = 0; index < 65; ++index) {
            const auto subgraph = makeScalarLeafPrototype(1024);
            subgraphs.push_back(subgraph);
            records.push_back(NamedSymbolPrototype(
                module, indexedName("parameter_warmup_", index),
                makeRecord(
                    "cdecl32", makeCallbackWrapper(subgraph), 0)));
        }

        std::vector<ParameterDescription> combinedParameters;
        combinedParameters.reserve(subgraphs.size());
        for (const auto &subgraph : subgraphs) {
            combinedParameters.push_back(ParameterDescription(
                text("callback"), pointerType(32, "callback_pointer"),
                ParameterDescription::PointeeAccess::NONE, subgraph));
        }
        const auto combined = std::make_shared<const FunctionPrototype>(
            voidType, std::move(combinedParameters), QString(), QString(),
            true, text("cdecl32"));
        records.push_back(NamedSymbolPrototype(
            module, text("parameter_combined"),
            makeRecord("cdecl32", combined, 0)));

        RecordingProvider provider(
            text("parameter-budget-provider"), 10, std::move(records));
        SymbolPrototypeRegistry registry;
        registry.addProvider(provider, SymbolPrototypeTarget(
            text("x86"), text("windows"), 32));

        check(registry.lookup(
                  module, text("parameter_warmup_0")) != nullptr &&
                  registry.lookup(
                      module, text("parameter_warmup_64")) != nullptr,
              "individually valid parameter-budget warmup records were rejected");
        check(registry.lookup(module, text("parameter_combined")) == nullptr,
              "cached subgraphs bypassed the per-record parameter-visit budget");
    }
}

void testPriorityAndConflictPolicy() {
    SymbolPrototypeRegistry registry;
    const QString module = text("runtime.priority");
    const QString name = text("combine_records");

    check(registry.add(
              module, name,
              makeRecord("baseline_convention", makeParentPrototype(
                  false, makeCallbackPrototype(false))),
              10, text("baseline-provider")) ==
              SymbolPrototypeRegistry::ADDED,
          "the first record must be added");

    check(registry.add(
              module, name,
              makeRecord("ignored_convention", makeParentPrototype(
                  true, makeCallbackPrototype(true))),
              5, text("lower-provider")) ==
              SymbolPrototypeRegistry::IGNORED_LOWER_PRIORITY,
          "a lower-priority record must not replace an existing record");
    check(registry.lookup(module, name) != nullptr &&
              registry.lookup(module, name)->conventionName() ==
                  text("baseline_convention"),
          "ignoring a lower-priority record must preserve the winner");

    const auto winningPrototype = makeParentPrototype(
        true, makeCallbackPrototype(true));
    check(registry.add(
              module, name,
              makeRecord("winning_convention", winningPrototype),
              20, text("winning-provider")) ==
              SymbolPrototypeRegistry::REPLACED_LOWER_PRIORITY,
          "a higher-priority record must replace a lower-priority record");
    check(registry.lookup(module, name) != nullptr &&
              registry.lookup(module, name)->prototype() == winningPrototype,
          "qualified lookup must return the higher-priority record");

    check(registry.add(
              module, name,
              makeRecord("winning_convention", makeParentPrototype(
                  true, makeCallbackPrototype(true))),
              20, text("equivalent-provider")) ==
              SymbolPrototypeRegistry::EQUIVALENT,
          "structurally equal records at one priority must coexist");

    check(registry.add(
              module, name,
              makeRecord("conflicting_convention", makeParentPrototype(
                  true, makeCallbackPrototype(true))),
              20, text("conflicting-provider")) ==
              SymbolPrototypeRegistry::CONFLICT,
          "different records at one priority must conflict");
    check(registry.hasConflict(module, name),
          "an equal-priority disagreement must be recorded");
    check(registry.lookup(module, name) == nullptr,
          "lookup must fail closed while the winning priority is ambiguous");

    check(registry.add(
              module, name,
              makeRecord("lower_after_conflict", makeParentPrototype(
                  false, makeCallbackPrototype(false))),
              15, text("late-lower-provider")) ==
              SymbolPrototypeRegistry::IGNORED_LOWER_PRIORITY,
          "a lower-priority record must not resolve a higher-priority conflict");
    check(registry.lookup(module, name) == nullptr,
          "a lower-priority record must not reopen conflicted metadata");

    check(registry.add(
              module, name,
              makeRecord("resolved_convention", makeParentPrototype(
                  true, makeCallbackPrototype(true))),
              30, text("resolution-provider")) ==
              SymbolPrototypeRegistry::REPLACED_LOWER_PRIORITY,
          "a strictly higher-priority record may resolve a conflict");
    check(!registry.hasConflict(module, name) &&
              registry.lookup(module, name) != nullptr &&
              registry.lookup(module, name)->conventionName() ==
                  text("resolved_convention"),
          "replacement by a higher priority must clear stale ambiguity");
}

void testPrototypeCompletenessParticipatesInEquality() {
    SymbolPrototypeRegistry registry;
    const QString module = text("runtime.effects");
    const QString name = text("visit_state");

    check(registry.add(
              module, name,
              makeRecord("effect_convention", makeParentPrototype(
                  true, makeCallbackPrototype(true))),
              10, text("complete-provider")) ==
              SymbolPrototypeRegistry::ADDED,
          "the complete prototype must be accepted initially");
    check(registry.add(
              module, name,
              makeRecord("effect_convention", makeParentPrototype(
                  false, makeCallbackPrototype(true))),
              10, text("incomplete-provider")) ==
              SymbolPrototypeRegistry::CONFLICT,
          "memory-effect completeness must participate in prototype equality");
    check(registry.lookup(module, name) == nullptr,
          "different completeness claims must fail closed");
}

void testCallbackPrototypeStructuralEquality() {
    const QString module = text("runtime.callbacks");
    const QString name = text("walk_records");

    {
        SymbolPrototypeRegistry registry;
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(true))),
                  50, text("first-provider")) ==
                  SymbolPrototypeRegistry::ADDED,
              "the first callback-bearing prototype must be added");
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(true))),
                  50, text("second-provider")) ==
                  SymbolPrototypeRegistry::EQUIVALENT,
              "separately allocated but structurally equal callbacks must match");
        check(registry.lookup(module, name) != nullptr,
              "equivalent callback metadata must remain usable");
    }

    {
        SymbolPrototypeRegistry registry;
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(true, 32))),
                  50, text("narrow-callback-provider")) ==
                  SymbolPrototypeRegistry::ADDED,
              "the first nested callback contract must be added");
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(true, 64))),
                  50, text("wide-callback-provider")) ==
                  SymbolPrototypeRegistry::CONFLICT,
              "a nested callback signature difference must conflict");
        check(registry.hasConflict(module, name) &&
                  registry.lookup(module, name) == nullptr,
              "conflicting callback contracts must fail closed");
    }

    {
        SymbolPrototypeRegistry registry;
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(
                          true, 32, "callback_abi"))),
                  50, text("first-abi-provider")) ==
                  SymbolPrototypeRegistry::ADDED,
              "the first callback ABI contract must be added");
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(
                          true, 32, "different_callback_abi"))),
                  50, text("second-abi-provider")) ==
                  SymbolPrototypeRegistry::CONFLICT,
              "a nested callback ABI difference must conflict");
    }

    {
        SymbolPrototypeRegistry registry;
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(
                          true, 32, "callback_abi", false))),
                  50, text("fixed-callback-provider")) ==
                  SymbolPrototypeRegistry::ADDED,
              "the fixed callback contract must be added");
        check(registry.add(
                  module, name,
                  makeRecord("callback_parent", makeParentPrototype(
                      true, makeCallbackPrototype(
                          true, 32, "callback_abi", true))),
                  50, text("variadic-callback-provider")) ==
                  SymbolPrototypeRegistry::CONFLICT,
              "a nested callback variadic difference must conflict");
    }
}

void testRegistryPreservesExactKeys() {
    SymbolPrototypeRegistry registry;
    const QString module = text(" runtime.exact ");
    const QString name = text(" operation ");
    check(registry.add(
              module, name,
              makeRecord("exact_convention", makeParentPrototype(
                  true, makeCallbackPrototype(true))),
              10, text("exact-provider")) ==
              SymbolPrototypeRegistry::ADDED,
          "an exact non-empty registry key must be accepted");
    check(registry.lookup(module, name) != nullptr,
          "the registry rewrote an exact provider key");
    check(registry.lookup(
              text("runtime.exact"), text("operation")) == nullptr,
          "trimmed lookup unexpectedly matched a distinct exact key");
}

} // anonymous namespace

int main() {
    try {
        testProviderReceivesTargetAndPopulatesRegistry();
        testProgrammaticProviderCannotBypassTargetLayout();
        testSharedCallbackDagValidationIsBounded();
        testSharedCallbackDagEquivalenceIsBounded();
        testCallbackChainBeyondDepthLimitFailsClosed();
        testAdversarialPrototypePairExpansionFailsClosed();
        testProviderAcceptsManyShallowRecords();
        testProviderBudgetsAreRecountedForEveryRecord();
        testPriorityAndConflictPolicy();
        testPrototypeCompletenessParticipatesInEquality();
        testCallbackPrototypeStructuralEquality();
        testRegistryPreservesExactKeys();
    } catch (const std::exception &exception) {
        std::cerr << "symbol prototype registry regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
