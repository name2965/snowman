add_executable(nc-analysis-regression-tests
    AnalysisRegressionTests.cpp
)

target_link_libraries(nc-analysis-regression-tests nc)

add_executable(nc-memory-fill-regression-tests
    MemoryFillRegressionTests.cpp
)

target_link_libraries(nc-memory-fill-regression-tests nc)

add_executable(nc-comparison-switch-regression-tests
    ComparisonSwitchRegressionTests.cpp
)

target_link_libraries(nc-comparison-switch-regression-tests nc)

add_executable(nc-symbol-prototype-registry-regression-tests
    SymbolPrototypeRegistryRegressionTests.cpp
)

target_link_libraries(nc-symbol-prototype-registry-regression-tests nc)

add_executable(nc-declarative-symbol-prototype-provider-regression-tests
    DeclarativeSymbolPrototypeProviderRegressionTests.cpp
)

target_link_libraries(
    nc-declarative-symbol-prototype-provider-regression-tests nc)

add_executable(nc-master-analyzer-refinement-regression-tests
    MasterAnalyzerRefinementRegressionTests.cpp
)

target_link_libraries(nc-master-analyzer-refinement-regression-tests nc)

add_executable(nc-imported-function-resolver-regression-tests
    ImportedFunctionResolverRegressionTests.cpp
)

target_link_libraries(nc-imported-function-resolver-regression-tests nc)

add_executable(nc-x86-noreturn-refinement-regression-tests
    X86NoReturnRefinementRegressionTests.cpp
)

target_link_libraries(nc-x86-noreturn-refinement-regression-tests nc)

add_executable(nc-definition-generator-regression-tests
    DefinitionGeneratorRegressionTests.cpp
)

target_link_libraries(nc-definition-generator-regression-tests nc)

add_executable(nc-pe-parser-regression-tests
    PeParserRegressionTests.cpp
)

target_link_libraries(nc-pe-parser-regression-tests nc)

add_executable(nc-cgen-identifier-regression-tests
    CgenIdentifierRegressionTests.cpp
)

target_link_libraries(nc-cgen-identifier-regression-tests nc)

add_test(
    NAME nc-analysis-regression
    COMMAND nc-analysis-regression-tests
)

add_test(
    NAME nc-memory-fill-regression
    COMMAND nc-memory-fill-regression-tests
)

add_test(
    NAME nc-comparison-switch-regression
    COMMAND nc-comparison-switch-regression-tests
)

add_test(
    NAME nc-symbol-prototype-registry-regression
    COMMAND nc-symbol-prototype-registry-regression-tests
)

add_test(
    NAME nc-declarative-symbol-prototype-provider-regression
    COMMAND nc-declarative-symbol-prototype-provider-regression-tests
)

add_test(
    NAME nc-master-analyzer-refinement-regression
    COMMAND nc-master-analyzer-refinement-regression-tests
)

add_test(
    NAME nc-imported-function-resolver-regression
    COMMAND nc-imported-function-resolver-regression-tests
)

add_test(
    NAME nc-x86-noreturn-refinement-regression
    COMMAND nc-x86-noreturn-refinement-regression-tests
)

add_test(
    NAME nc-definition-generator-regression
    COMMAND nc-definition-generator-regression-tests
)

add_test(
    NAME nc-pe-parser-regression
    COMMAND nc-pe-parser-regression-tests
)

add_test(
    NAME nc-cgen-identifier-regression
    COMMAND nc-cgen-identifier-regression-tests
)

# vim:set et sts=4 sw=4 nospell:
