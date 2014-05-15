cmake_minimum_required(VERSION 2.8)

include_directories (
	"${PROJECT_SOURCE_DIR}/src"
	"${PROJECT_SOURCE_DIR}/lib/gtest-1.6.0/include/"
	"${PROJECT_SOURCE_DIR}/lib/pluscallback1.7/"
	"${PROJECT_BINARY_DIR}/tests/"
)

MESSAGE(STATUS "building minisatid tests ${BUILDTESTS}")

if(${BUILDTESTS})
	addToCXX("-Wall -pedantic -std=c++0x")
	if(CMAKE_COMPILER_IS_GNUCXX)
		addToCXX("-Wextra")
	endif()
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D MINISATIDTESTDIR=\\\"${PROJECT_SOURCE_DIR}/tests/instances\\\" ")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=gnu++0x") #necessary for gtest!
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D TESTDIR=\\\"${PROJECT_SOURCE_DIR}/tests\\\" ")
	addToCXX("-D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS")
	
	if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D__STRICT_ANSI__")
    endif()
		
	add_executable(mtests 
		TestUtils.cpp
		TestSuite.cpp
		Mxtests.cpp
		Cptests.cpp
		Janhunentest.cpp
	)
	
	target_link_libraries(mtests minisatid gtest)
	if(UNIX)
		set_target_properties(mtests PROPERTIES LINK_FLAGS "-pthread ")
	endif()
	add_test(mtests mtests "--gtest_color=yes")
	add_custom_target(minicheck COMMAND ${CMAKE_CTEST_COMMAND} -V DEPENDS mtests)
endif()