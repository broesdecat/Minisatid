cmake_minimum_required(VERSION 2.8)

include_directories ("
	"${PROJECT_SOURCE_DIR}/src"
	"${PROJECT_SOURCE_DIR}/lib/gtest-1.6.0/include/"
	"${PROJECT_SOURCE_DIR}/lib/pluscallback1.7/"
")

MESSAGE(STATUS "building minisatid tests ${BUILDTESTS}")

if(${BUILDTESTS})
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D MINISATIDTESTDIR=\\\"${PROJECT_SOURCE_DIR}/tests\\\" ")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=gnu++0x") #necessary for gtest!
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D TESTDIR=\\\"${PROJECT_SOURCE_DIR}/tests\\\" ")
	addToCXX("-D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS")
	
	find_package(BISON)
	find_package(FLEX)
	
	BISON_TARGET(myparser ${PROJECT_SOURCE_DIR}/src/parser/ecnfparser.ypp ${CMAKE_CURRENT_BINARY_DIR}/parser.cc)
	FLEX_TARGET(myscanner ${PROJECT_SOURCE_DIR}/src/parser/ecnftoken.lpp  ${CMAKE_CURRENT_BINARY_DIR}/lexer.cc)
	ADD_FLEX_BISON_DEPENDENCY(myscanner myparser)
	
	add_executable(mtests 
		TestUtils.cpp
		TestSuite.cpp
		Mxtests.cpp
		Cptests.cpp
		Janhunentest.cpp
		${PROJECT_SOURCE_DIR}/src/Run.cpp
		${PROJECT_SOURCE_DIR}/src/Run.hpp
		${BISON_myparser_OUTPUTS} ${FLEX_myscanner_OUTPUTS}
	)
	
	target_link_libraries(mtests minisatid gtest)
	if(UNIX)
		set_target_properties(mtests PROPERTIES LINK_FLAGS "-pthread ")
	endif()
	add_test(mtests mtests "--gtest_color=yes")
	add_custom_target(minicheck COMMAND ${CMAKE_CTEST_COMMAND} -V DEPENDS mtests)
endif()