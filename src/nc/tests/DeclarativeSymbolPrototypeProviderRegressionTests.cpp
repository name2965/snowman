/* The file is part of Snowman decompiler. */
/* See doc/licenses.asciidoc for the licensing information. */

#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include <QLatin1String>
#include <QString>

#include <nc/core/ir/calling/DeclarativeSymbolPrototypeProvider.h>
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

const char VALID_DOCUMENT[] = R"json(
{
  "schema": "snowman.symbol-prototypes",
  "schema_version": 1,
  "provider": {
    "id": "generated-test-contracts",
    "priority": 27
  },
  "targets": [
    {
      "architecture": "synthetic-cpu",
      "operating_system": "research-os",
      "bitness": 32,
      "symbols": [
        {
          "module": "runtime.alpha",
          "name": "dispatch_record",
          "convention": "callee-cleanup-32",
          "stack_arguments_size": 8,
          "noreturn": true,
          "prototype": {
            "return_type": {
              "kind": "integer",
              "size": 32,
              "unsigned": false,
              "display_name": "dispatch_result"
            },
            "parameters": [
              {
                "name": "state",
                "type": {
                  "kind": "pointer",
                  "size": 32,
                  "unsigned": true,
                  "display_name": "state_pointer"
                },
                "pointee_access": "read"
              },
              {
                "name": "visitor",
                "type": {
                  "kind": "pointer",
                  "size": 32,
                  "unsigned": true,
                  "display_name": "visitor_pointer"
                },
                "pointee_access": "none",
                "callback": {
                  "return_type": {
                    "kind": "integer",
                    "size": 32,
                    "unsigned": true,
                    "display_name": "visit_result"
                  },
                  "parameters": [
                    {
                      "name": "item",
                      "type": {
                        "kind": "pointer",
                        "size": 32,
                        "unsigned": true
                      },
                      "pointee_access": "read_write"
                    }
                  ],
                  "abi_convention": "callback-abi",
                  "source_calling_convention": "callback_cc",
                  "preferred_name": "record_visitor",
                  "memory_effects_complete": false
                }
              }
            ],
            "source_calling_convention": "source_cc",
            "preferred_name": "dispatch_contract",
            "memory_effects_complete": true
          }
        },
        {
          "module": "runtime.alpha",
          "name": "inspect_record",
          "convention": "caller-cleanup-32",
          "prototype": {
            "return_type": {
              "kind": "void",
              "size": 0,
              "unsigned": false
            },
            "parameters": [
              {
                "name": "buffer",
                "type": {
                  "kind": "pointer",
                  "size": 32,
                  "unsigned": true
                }
              }
            ],
            "variadic": true
          }
        }
      ]
    },
    {
      "architecture": "synthetic-cpu",
      "operating_system": "research-os",
      "bitness": 64,
      "symbols": [
        {
          "module": "runtime.beta",
          "name": "wide_operation",
          "convention": "register-64",
          "prototype": {
            "return_type": {
              "kind": "pointer",
              "size": 64,
              "unsigned": true
            },
            "parameters": []
          }
        }
      ]
    }
  ]
}
)json";

void testValidDocumentAndExactTargetSelection() {
    QString error;
    const auto provider =
        DeclarativeSymbolPrototypeProvider::fromJson(
            std::string(VALID_DOCUMENT), &error);
    check(provider != nullptr, "a valid version-one document must parse");
    check(error.isEmpty(), "successful parsing must clear the diagnostic");
    check(provider->id() == text("generated-test-contracts"),
          "provider id must come from the document");
    check(provider->priority() == 27,
          "provider priority must come from the document");

    const std::vector<NamedSymbolPrototype> records =
        provider->getPrototypes(SymbolPrototypeTarget(
            text("synthetic-cpu"), text("research-os"), 32));
    check(records.size() == 2,
          "only records for the exact target must be returned");
    check(provider->prototypeCount(SymbolPrototypeTarget(
              text("synthetic-cpu"), text("research-os"), 32)) == 2,
          "target diagnostics must report the exact record count without "
          "altering selection");
    check(records[0].moduleName() == text("runtime.alpha") &&
              records[0].name() == text("dispatch_record"),
          "module and symbol names must be retained exactly");

    const SymbolPrototypeRecord &record = records[0].record();
    check(record.conventionName() == text("callee-cleanup-32"),
          "the internal convention name must be retained");
    check(record.stackArgumentsSize() &&
              *record.stackArgumentsSize() == 8,
          "an explicit stack argument size must be retained");
    check(record.doesNotReturn(),
          "an explicit noreturn contract must be retained");
    check(record.prototype() != nullptr &&
              record.prototype()->memoryEffectsAreComplete(),
          "an explicit complete memory-effect contract must be retained");
    check(!record.prototype()->variadic(),
          "variadic must default to false");
    check(record.prototype()->callingConvention() == text("source_cc") &&
              record.prototype()->preferredName() ==
                  text("dispatch_contract"),
          "source-level prototype metadata must be retained");
    check(record.prototype()->returnType().kind() ==
              TypeDescription::INTEGER &&
              record.prototype()->returnType().size() == 32 &&
              !record.prototype()->returnType().isUnsigned(),
          "the return scalar type must be decoded exactly");

    const auto &parameters = record.prototype()->parameters();
    check(parameters.size() == 2 &&
              parameters[0].name() == text("state") &&
              parameters[0].mayReadMemory() &&
              !parameters[0].mayWriteMemory(),
          "parameter names, types and pointee effects must be decoded");
    check(parameters[1].callbackPrototype() != nullptr,
          "nested callback prototypes must be decoded");
    check(parameters[1].callbackPrototype()->callingConvention() ==
              text("callback_cc") &&
              parameters[1].callbackPrototype()->abiConventionName() ==
                  text("callback-abi") &&
              parameters[1].callbackPrototype()->preferredName() ==
                  text("record_visitor"),
          "nested callback metadata must be retained");

    const std::vector<NamedSymbolPrototype> wideRecords =
        provider->getPrototypes(SymbolPrototypeTarget(
            text("synthetic-cpu"), text("research-os"), 64));
    check(wideRecords.size() == 1 &&
              wideRecords.front().name() == text("wide_operation"),
          "bitness must participate in exact target selection");
    check(provider->getPrototypes(SymbolPrototypeTarget(
              text("synthetic-cpu"), text("other-os"), 32)).empty(),
          "a provider must not fall back across operating systems");
    check(provider->getPrototypes(SymbolPrototypeTarget(
              text("other-cpu"), text("research-os"), 32)).empty(),
          "a provider must not fall back across architectures");
    check(provider->prototypeCount(SymbolPrototypeTarget(
              text("other-cpu"), text("research-os"), 32)) == 0,
          "target diagnostics must not fall back across architectures");
}

void testConservativeDefaultsAndRegistryIntegration() {
    const auto provider =
        DeclarativeSymbolPrototypeProvider::fromJson(
            std::string(VALID_DOCUMENT));
    check(provider != nullptr, "the fixture must parse without a diagnostic");

    const SymbolPrototypeTarget target(
        text("synthetic-cpu"), text("research-os"), 32);
    const auto records = provider->getPrototypes(target);
    const SymbolPrototypeRecord &record = records[1].record();
    check(!record.stackArgumentsSize(),
          "an omitted stack extent must remain unknown");
    check(!record.doesNotReturn(),
          "noreturn must default to false");
    check(!record.prototype()->memoryEffectsAreComplete(),
          "memory-effect completeness must default to false");
    check(record.prototype()->variadic(),
          "an explicit variadic contract must be retained");
    check(record.prototype()->parameters().front().mayReadMemory() &&
              record.prototype()->parameters().front().mayWriteMemory(),
          "an unspecified pointer effect must conservatively be read-write");

    SymbolPrototypeRegistry registry;
    registry.addProvider(*provider, target);
    const SymbolPrototypeRecord *lookup = registry.lookup(
        text("runtime.alpha"), text("inspect_record"));
    check(lookup != nullptr &&
              lookup->conventionName() == text("caller-cleanup-32"),
          "parsed records must integrate with exact registry lookup");
    check(registry.lookup(text("inspect_record")) == nullptr,
          "a qualified declarative record must not become a fallback entry");
}

void testRegistryOwnsProviderResults() {
    SymbolPrototypeRegistry registry;
    std::weak_ptr<const FunctionPrototype> prototypeLifetime;

    {
        const auto provider =
            DeclarativeSymbolPrototypeProvider::fromJson(
                std::string(VALID_DOCUMENT));
        check(provider != nullptr, "the fixture must parse");

        const SymbolPrototypeTarget target(
            text("synthetic-cpu"), text("research-os"), 32);
        const auto records = provider->getPrototypes(target);
        prototypeLifetime = records.front().record().prototype();
        registry.addProvider(*provider, target);
    }

    check(!prototypeLifetime.expired(),
          "the registry must own copied prototype metadata after provider destruction");
    const SymbolPrototypeRecord *record = registry.lookup(
        text("runtime.alpha"), text("dispatch_record"));
    check(record != nullptr && record->prototype() != nullptr &&
              record->prototype()->parameters()[1].callbackPrototype() !=
                  nullptr,
          "registry records must not retain references into provider storage");
}

void checkRejected(const std::string &json, const char *message) {
    QString error;
    const auto provider =
        DeclarativeSymbolPrototypeProvider::fromJson(json, &error);
    check(provider == nullptr, message);
    check(!error.isEmpty(),
          "a rejected document must provide a diagnostic");
}

std::string minimalDocument(const std::string &symbolMember) {
    return std::string(R"json({
      "schema":"snowman.symbol-prototypes",
      "schema_version":1,
      "provider":{"id":"strict-provider","priority":0},
      "targets":[{
        "architecture":"test-cpu",
        "operating_system":"test-os",
        "bitness":32,
        "symbols":[{)json") + symbolMember + R"json(}]
      }]
    })json";
}

void testMalformedAndUnsupportedDocumentsFailClosed() {
    checkRejected("{", "malformed JSON must be rejected");
    checkRejected(R"json({
      "schema":"other.schema", "schema_version":1,
      "provider":{"id":"p","priority":0}, "targets":[]
    })json", "an unknown schema id must be rejected");
    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes", "schema_version":2,
      "provider":{"id":"p","priority":0}, "targets":[]
    })json", "an unsupported schema version must be rejected");
    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes", "schema_version":"1",
      "provider":{"id":"p","priority":0}, "targets":[]
    })json", "a quoted schema version must not pass as a number");
    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes", "schema_version":1,
      "provider":{"id":"p","priority":0}, "targets":[],
      "extension":true
    })json", "unknown root members must be rejected");
    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes",
      "schema":"snowman.symbol-prototypes", "schema_version":1,
      "provider":{"id":"p","priority":0}, "targets":[]
    })json", "duplicate members must be rejected");

    checkRejected(minimalDocument(R"json(
      "module":"", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "an empty exact module name must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":" ", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "whitespace must not become an unqualified module fallback");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":" operation ", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "an exact symbol name must not be silently trimmed");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "stack_arguments_size":-1,
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "a negative stack extent must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "noreturn":"maybe",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "an invalid boolean must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "noreturn":"true",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "a quoted boolean must not pass as a boolean");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "stack_arguments_size":"4",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}
    )json"), "a quoted stack extent must not pass as a number");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"floating","size":32,
      "unsigned":false},"parameters":[]}
    )json"), "an unsupported scalar kind must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"bad",
      "type":{"kind":"void","size":0,"unsigned":false}}]}
    )json"), "a void parameter must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"count",
      "type":{"kind":"integer","size":32,"unsigned":false},
      "pointee_access":"read"}]}
    )json"), "pointee effects on a non-pointer must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"wide",
      "type":{"kind":"integer","size":64,"unsigned":false}}]}
    )json"), "a scalar wider than one target ABI slot must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"wrong_pointer",
      "type":{"kind":"pointer","size":64,"unsigned":true}}]}
    )json"), "a pointer size different from target bitness must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[],"unexpected":0}
    )json"), "unknown nested members must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"callback",
      "type":{"kind":"pointer","size":32,"unsigned":true},
      "callback":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[]}}]}
    )json"), "a callback without an explicit target ABI must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"abi_convention":"cdecl32",
      "return_type":{"kind":"void","size":0,"unsigned":false},
      "parameters":[]}
    )json"), "a top-level prototype must not duplicate the symbol ABI");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"bad-name",
      "type":{"kind":"integer","size":32,"unsigned":false}}]}
    )json"), "parameter names must be safe source identifiers");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[
      {"name":"value","type":{"kind":"integer","size":32,
      "unsigned":false}},{"name":"value","type":{"kind":"integer",
      "size":32,"unsigned":false}}]}
    )json"), "duplicate parameter identifiers must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"integer","size":32,
      "unsigned":false,"display_name":"bad type"},"parameters":[]}
    )json"), "verbatim type spellings must be safe single tokens");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"pointer","size":32,
      "unsigned":true,"display_name":"int"},"parameters":[]}
    )json"), "a built-in integer spelling must not erase pointer kind");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"integer","size":32,
      "unsigned":true,"display_name":"int"},"parameters":[]}
    )json"), "a built-in spelling must preserve integer signedness");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"integer","size":32,
      "unsigned":false,"display_name":""},"parameters":[]}
    )json"), "an explicitly empty optional identifier must be rejected");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[],"preferred_name":"if"}
    )json"), "preferred names must not be C/C++ keywords");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[],
      "source_calling_convention":"__stdcall)"}
    )json"), "source calling-convention spellings must be safe tokens");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[],"variadic":"true"}
    )json"), "a quoted variadic flag must not pass as a boolean");
    checkRejected(minimalDocument(R"json(
      "module":"m", "name":"operation", "convention":"cc",
      "stack_arguments_size":4,
      "prototype":{"return_type":{"kind":"void","size":0,
      "unsigned":false},"parameters":[{"name":"format",
      "type":{"kind":"pointer","size":32,"unsigned":true}}],
      "variadic":true}
    )json"), "a variadic contract must not assert a fixed total stack extent");
}

void testDuplicateSelectorsAndRecordsFailClosed() {
    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes", "schema_version":1,
      "provider":{"id":"duplicates","priority":1},
      "targets":[
        {"architecture":"cpu","operating_system":"os","bitness":32,
         "symbols":[{"module":"a","name":"f","convention":"cc",
          "prototype":{"return_type":{"kind":"void","size":0,
          "unsigned":false},"parameters":[]}}]},
        {"architecture":"cpu","operating_system":"os","bitness":32,
         "symbols":[{"module":"b","name":"g","convention":"cc",
          "prototype":{"return_type":{"kind":"void","size":0,
          "unsigned":false},"parameters":[]}}]}
      ]
    })json", "duplicate target selectors must reject the whole provider");

    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes", "schema_version":1,
      "provider":{"id":"duplicates","priority":1},
      "targets":[{"architecture":"cpu","operating_system":"os",
       "bitness":32,"symbols":[
        {"module":"a","name":"f","convention":"cc",
         "prototype":{"return_type":{"kind":"void","size":0,
         "unsigned":false},"parameters":[]}},
        {"module":"a","name":"f","convention":"other-cc",
         "prototype":{"return_type":{"kind":"void","size":0,
         "unsigned":false},"parameters":[]}}
       ]}]
    })json", "duplicate exact module/name records must reject the provider");
}

void testWindowsModuleKeysMustMatchRuntimeCanonicalization() {
    checkRejected(R"json({
      "schema":"snowman.symbol-prototypes", "schema_version":1,
      "provider":{"id":"windows-keys","priority":1},
      "targets":[{"architecture":"x86","operating_system":"windows",
       "bitness":32,"symbols":[
        {"module":"Example.DLL","name":"operation","convention":"cdecl32",
         "prototype":{"return_type":{"kind":"void","size":0,
         "unsigned":false},"parameters":[]}}
       ]}]
    })json",
        "a Windows module key which cannot match the lower-case runtime key "
        "must be rejected");

    QString error;
    const auto provider = DeclarativeSymbolPrototypeProvider::fromJson(
        R"json({
          "schema":"snowman.symbol-prototypes", "schema_version":1,
          "provider":{"id":"windows-keys","priority":1},
          "targets":[{"architecture":"x86","operating_system":"windows",
           "bitness":32,"symbols":[
            {"module":"example.dll","name":"operation",
             "convention":"cdecl32",
             "prototype":{"return_type":{"kind":"void","size":0,
             "unsigned":false},"parameters":[]}}
           ]}]
        })json",
        &error);
    check(provider != nullptr && error.isEmpty(),
          "a lower-case Windows module key must remain valid");
}

} // anonymous namespace

int main() {
    try {
        testValidDocumentAndExactTargetSelection();
        testConservativeDefaultsAndRegistryIntegration();
        testRegistryOwnsProviderResults();
        testMalformedAndUnsupportedDocumentsFailClosed();
        testDuplicateSelectorsAndRecordsFailClosed();
        testWindowsModuleKeysMustMatchRuntimeCanonicalization();
    } catch (const std::exception &exception) {
        std::cerr << "declarative prototype provider regression test failed: "
                  << exception.what() << std::endl;
        return 1;
    }
    return 0;
}

/* vim:set et sts=4 sw=4: */
