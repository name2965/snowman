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

# vim:set et sts=4 sw=4 nospell:
