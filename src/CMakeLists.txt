cmake_minimum_required(VERSION 2.8.6)

include_directories (
	"${PROJECT_SOURCE_DIR}/src/"
	"${PROJECT_BINARY_DIR}/src/"
	"${PROJECT_SOURCE_DIR}/lib/tclap/include"
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/ADTs" 
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/pbbase/h" 
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/"
	
)
if(DEFINED FLEX_INCLUDE_DIR)
    include_directories("${FLEX_INCLUDE_DIR}")
endif()

addToCXX("-Wall -pedantic -std=c++0x")
if(CMAKE_COMPILER_IS_GNUCXX)
	addToCXX("-Wextra")
endif()
if(CMAKE_COMPILER_IS_CLANG)
	addToCXX("-Wno-overloaded-virtual")
endif()

if(CMAKE_COMPILER_IS_MINGW)
	message(STATUS "Mingw compiler")
	addToCXX("-static-libgcc -static-libstdc++ ")
	addToCXX("-Wl,--stack,4194304")
endif()

addToCXX("-D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D VERSION=\\\"${MinisatID_VERSION_MAJOR}-${MinisatID_VERSION_MINOR}-${MinisatID_VERSION_PATCH}\\\"")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D DATADIR=\"\\\"${CMAKE_INSTALL_PREFIX}/var/minisatid\\\"\"")

set(LIBMINISATIDCPPFILES "")
file(GLOB_RECURSE LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/*.cpp")
file(GLOB_RECURSE LIBMINISATIDHPPFILES "${PROJECT_SOURCE_DIR}/src/*.hpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/Main.cpp")

find_package(BISON)
find_package(FLEX)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/ecnfparser)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/fzparser)
BISON_TARGET(ecnfparser parser/ecnfparser.ypp ${CMAKE_CURRENT_BINARY_DIR}/ecnfparser/ecnfparser.cc)
FLEX_TARGET(ecnfscanner parser/ecnftoken.lpp  ${CMAKE_CURRENT_BINARY_DIR}/ecnfparser/ecnflexer.cc)
ADD_FLEX_BISON_DEPENDENCY(ecnfscanner ecnfparser)
BISON_TARGET(fzparser parser/flatzincparser.ypp ${CMAKE_CURRENT_BINARY_DIR}/fzparser/fzparser.cc)
FLEX_TARGET(fzscanner parser/flatzinclexer.lpp  ${CMAKE_CURRENT_BINARY_DIR}/fzparser/fzlexer.cc)
ADD_FLEX_BISON_DEPENDENCY(fzscanner fzparser)

add_library(minisatid
	${LIBMINISATIDCPPFILES}
	${LIBMINISATIDHPPFILES}
	${BISON_ecnfparser_OUTPUTS} ${FLEX_ecnfscanner_OUTPUTS}
	${BISON_fzparser_OUTPUTS} ${FLEX_fzscanner_OUTPUTS}
)

set(LIBS ${LIBS} pbsolver)
target_link_libraries(minisatid ${LIBS})
if(GPERF)
	target_link_libraries(minisatid tcmalloc_and_profiler)
endif()

add_executable(minisatid-bin 
		Main.cpp
)
target_link_libraries(minisatid-bin pbsolver minisatid)
if(GPERF)
	target_link_libraries(minisatid-bin tcmalloc_and_profiler)
endif()

set_target_properties(minisatid-bin PROPERTIES OUTPUT_NAME minisatid)

if(BUILD_MINISATID_STATIC)
	set_target_properties(minisatid PROPERTIES LINK_FLAGS "-static ")
	set_target_properties(minisatid-bin PROPERTIES LINK_FLAGS "-static ")
endif()

set_target_properties(
	minisatid minisatid-bin PROPERTIES
	VERSION ${MinisatID_VERSION}
)

# add the install targets
install (TARGETS minisatid minisatid-bin 
	RUNTIME DESTINATION bin
	LIBRARY DESTINATION lib
	ARCHIVE DESTINATION lib
)

message(STATUS "Options:")
message(STATUS "General minisatid options: ${CMAKE_CXX_FLAGS}")
