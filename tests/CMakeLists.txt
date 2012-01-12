cmake_minimum_required(VERSION 2.8)

include_directories ("
	"${PROJECT_SOURCE_DIR}/src"
	"${PROJECT_SOURCE_DIR}/lib/gtest-1.6.0/include/"
")

MESSAGE(STATUS "building minisatid tests ${BUILDTESTS}")

if(${BUILDTESTS})
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=gnu++0x") #necessary for gtest!
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D TESTDIR=\\\"${PROJECT_SOURCE_DIR}/tests\\\" ")
	add_executable(mtests tests/googletestsnippet.cpp tests/janhunentest.cpp)
	target_link_libraries(mtests minisatid gtest)
	set_target_properties(mtests PROPERTIES LINK_FLAGS "-pthread ")
	add_test(mtests mtests "--gtest_color=yes")
	add_custom_target(check COMMAND ${CMAKE_CTEST_COMMAND} -V DEPENDS mtests)
endif()