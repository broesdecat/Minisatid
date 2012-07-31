cmake_minimum_required(VERSION 2.8)

include_directories (
	"${PROJECT_SOURCE_DIR}/src/"
	"${PROJECT_BINARY_DIR}/src/"
	"${PROJECT_SOURCE_DIR}/lib/pluscallback1.7/"
	"${PROJECT_SOURCE_DIR}/lib/tclap/include"
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/ADTs" 
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/pbbase/h" 
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/"
)

macro(addToCXX ARGUMENT) #NOTE do not use when escape characters are important
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${ARGUMENT}")
endmacro()

addToCXX("-std=c++0x")
addToCXX("-D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D VERSION=\\\"${MinisatID_VERSION_MAJOR}-${MinisatID_VERSION_MINOR}-${MinisatID_VERSION_PATCH}\\\"")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D DATADIR=\"\\\"${CMAKE_INSTALL_PREFIX}/var/minisatid\\\"\"")

# CP interface
file(GLOB_RECURSE CP_SOURCES "${PROJECT_SOURCE_DIR}/src/modules/cpsolver/*.cpp")
list(APPEND CP_SOURCES "${PROJECT_SOURCE_DIR}/src/modules/CPSolver.cpp")
file(GLOB_RECURSE CP_HEADERS "${PROJECT_SOURCE_DIR}/src/modules/cpsolver/*.hpp")
list(APPEND CP_HEADERS "${PROJECT_SOURCE_DIR}/src/modules/CPSolver.hpp")
if(WITHGECODE)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D CPSUPPORT")
endif()

set(LIBMINISATIDCPPFILES "")
file(GLOB_RECURSE LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/*.cpp")
file(GLOB_RECURSE LIBMINISATIDHPPFILES "${PROJECT_SOURCE_DIR}/src/*.hpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/Main.cpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/Run.hpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/Run.cpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/parser/Parser.cpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/parser/Parser.hpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/parser/ECNFScanner.hpp")
LIST(REMOVE_ITEM LIBMINISATIDCPPFILES "${PROJECT_SOURCE_DIR}/src/parser/ECNFScanner.cpp")
if(NOT WITHGECODE)
	LIST(REMOVE_ITEM LIBMINISATIDCPPFILES ${CP_SOURCES})
	LIST(REMOVE_ITEM LIBMINISATIDHPPFILES ${CP_HEADERS})
endif()

add_library(minisatid
	${LIBMINISATIDCPPFILES}
	${LIBMINISATIDHPPFILES}
)

set(LIBS ${LIBS} pbsolver)
target_link_libraries(minisatid ${LIBS})

find_package(BISON)
find_package(FLEX)

BISON_TARGET(myparser parser/ecnfparser.ypp ${CMAKE_CURRENT_BINARY_DIR}/parser.cc)
FLEX_TARGET(myscanner parser/ecnftoken.lpp  ${CMAKE_CURRENT_BINARY_DIR}/lexer.cc)
ADD_FLEX_BISON_DEPENDENCY(myscanner myparser)

add_executable(minisatid-bin Main.cpp Run.hpp Run.cpp parser/ECNFScanner.hpp parser/ECNFScanner.cpp parser/Parser.hpp parser/Parser.cpp ${BISON_myparser_OUTPUTS} ${FLEX_myscanner_OUTPUTS})
target_link_libraries(minisatid-bin pbsolver minisatid)
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
message(STATUS "use gecode support for cp ${WITHGECODE}")