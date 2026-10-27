set(MOC_HEADERS
    SnowmanView.h
)

set(SOURCES
    SnowmanView.cpp
    pluginmain.cpp
    pluginmain.h
    QtPlugin.cpp
    QtPlugin.h
    ${MOC_HEADERS}
)

include_directories(${X64DBG_SDK_PATH})

qt4_wrap_cpp(SOURCES ${MOC_HEADERS})
qt5_add_resources(SOURCES x64dbg-module.qrc)

if("${CMAKE_SIZEOF_VOID_P}" EQUAL "8")
    set(EXTENSION .dp64)
else()
    set(EXTENSION .dp32)
endif()

add_library(x64dbg-module SHARED ${SOURCES})
target_link_libraries(x64dbg-module nc-gui nc ${Boost_LIBRARIES} ${QT_LIBRARIES} ${X64DBG_LIBRARY} ${X64BRIDGE_LIBRARY})
set_target_properties(x64dbg-module PROPERTIES OUTPUT_NAME "snowman" PREFIX "" SUFFIX ${EXTENSION})
install(TARGETS x64dbg-module RUNTIME DESTINATION bin LIBRARY DESTINATION lib)

set(SNOWMAN_SYMBOL_PROTOTYPES_PATH "" CACHE FILEPATH
    "Generated symbol-prototype JSON to deploy beside the x64dbg module")
if(NOT SNOWMAN_SYMBOL_PROTOTYPES_PATH AND
   DEFINED ENV{SNOWMAN_SYMBOL_PROTOTYPES} AND
   NOT "$ENV{SNOWMAN_SYMBOL_PROTOTYPES}" STREQUAL "")
    # Use the same override as the runtime loader. This keeps local builds
    # reproducible without baking a machine-specific path into the source
    # tree. Rechecking an empty cache entry also makes setting the environment
    # variable after an initial configure do what the user expects; a nonempty
    # explicit -D value still wins.
    set(SNOWMAN_SYMBOL_PROTOTYPES_PATH
        "$ENV{SNOWMAN_SYMBOL_PROTOTYPES}" CACHE FILEPATH
        "Generated symbol-prototype JSON to deploy beside the x64dbg module"
        FORCE)
endif()

option(SNOWMAN_REQUIRE_SYMBOL_PROTOTYPES
    "Fail configuration when the x64dbg module has no prototype catalog"
    OFF)

if(SNOWMAN_SYMBOL_PROTOTYPES_PATH)
    if(NOT IS_ABSOLUTE "${SNOWMAN_SYMBOL_PROTOTYPES_PATH}")
        message(FATAL_ERROR
            "SNOWMAN_SYMBOL_PROTOTYPES_PATH must be absolute: ${SNOWMAN_SYMBOL_PROTOTYPES_PATH}")
    elseif(NOT EXISTS "${SNOWMAN_SYMBOL_PROTOTYPES_PATH}" OR
       IS_DIRECTORY "${SNOWMAN_SYMBOL_PROTOTYPES_PATH}")
        message(FATAL_ERROR
            "SNOWMAN_SYMBOL_PROTOTYPES_PATH is not a file: ${SNOWMAN_SYMBOL_PROTOTYPES_PATH}")
    endif()
    # Attach deployment to the module itself. Building only the
    # x64dbg-module project in Visual Studio must produce a usable plugin,
    # rather than requiring an unrelated ALL target to be built as well.
    add_custom_command(TARGET x64dbg-module POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
            "${SNOWMAN_SYMBOL_PROTOTYPES_PATH}"
            "$<TARGET_FILE_DIR:x64dbg-module>/snowman-symbol-prototypes.json"
        VERBATIM)
    install(FILES "${SNOWMAN_SYMBOL_PROTOTYPES_PATH}"
        DESTINATION bin RENAME snowman-symbol-prototypes.json)
    message(STATUS
        "x64dbg symbol prototypes: ${SNOWMAN_SYMBOL_PROTOTYPES_PATH}")
elseif(SNOWMAN_REQUIRE_SYMBOL_PROTOTYPES)
    message(FATAL_ERROR
        "The x64dbg module requires an authoritative symbol-prototype "
        "catalog, but none was configured. Set "
        "SNOWMAN_SYMBOL_PROTOTYPES_PATH or the SNOWMAN_SYMBOL_PROTOTYPES "
        "environment variable to a generated schema-version-1 JSON file.")
else()
    message(WARNING
        "No authoritative symbol-prototype catalog will be deployed with "
        "the x64dbg module. External function names can still be recovered, "
        "but ABI types and parameter lists which machine code does not prove "
        "will remain conservative. Set SNOWMAN_SYMBOL_PROTOTYPES_PATH, or "
        "enable SNOWMAN_REQUIRE_SYMBOL_PROTOTYPES to make this an error.")
endif()

# vim:set et sts=4 sw=4 nospell:
