/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

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
        bool memoryEffectsAreComplete, SmallBitSize resultSize = 32) {
    std::vector<ParameterDescription> parameters;
    parameters.push_back(ParameterDescription(
        text("context"), pointerType(64, "context_pointer"),
        ParameterDescription::PointeeAccess::READ));

    return std::make_shared<const FunctionPrototype>(
        integerType(resultSize, resultSize == 32 ?
            "callback_result" : "wide_callback_result"),
        std::move(parameters), text("callback_convention"),
        text("callback_contract"), memoryEffectsAreComplete);
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
}

} // anonymous namespace

int main() {
    try {
        testProviderReceivesTargetAndPopulatesRegistry();
        testPriorityAndConflictPolicy();
        testPrototypeCompletenessParticipatesInEquality();
        testCallbackPrototypeStructuralEquality();
    } catch (const std::exception &exception) {
        std::cerr << "symbol prototype registry regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }

    return 0;
}

/* vim:set et sts=4 sw=4: */
