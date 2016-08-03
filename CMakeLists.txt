cmake_minimum_required(VERSION 2.8)
project (minisatid)

# The version number.
set (MinisatID_VERSION_MAJOR 3)
set (MinisatID_VERSION_MINOR 12)
set (MinisatID_VERSION_PATCH 0)
set (MinisatID_VERSION "${MinisatID_VERSION_MAJOR}.${MinisatID_VERSION_MINOR}.${MinisatID_VERSION_PATCH}")

execute_process (COMMAND "git" "rev-parse" "HEAD"
                WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                RESULT_VARIABLE minisatid_git_result
				ERROR_VARIABLE minisatid_git_error
                OUTPUT_VARIABLE minisatid_git_hash)
if (minisatid_git_result OR minisatid_git_error)
  set (minisatid_git_hash "\"Source not version controlled.\"")
endif (minisatid_git_result OR minisatid_git_error)

string(STRIP ${minisatid_git_hash} minisatid_git_hash)

ENABLE_TESTING()

set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")

### Rpath handling
include(cmake/rpathhandling.cmake)

### Target properties helper
include(cmake/settargetproperties.cmake)

macro(addToCXX ARGUMENT)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${ARGUMENT}")
endmacro()

option(GPERF  "Enable profiling support with google-perftools" OFF)
if(GPERF)
	addToCXX("-fno-omit-frame-pointer")
endif()

OPTION(BUILDTESTS  		"Run the gtest tests" ON)
OPTION(GMP  			"Enable gmp support" OFF)

if(GMP)
	addToCXX("-D GMP")
	find_package(GMP)
	if(GMP_FOUND)
		include_directories(${GMP_INCLUDE_DIR})
		set(LIBS ${LIBS} ${GMP_LIBRARIES})
		set(LIBS ${LIBS} ${GMPXX_LIBRARIES})		
	else()
		message(FATAL_ERROR "GMP library not found")
	endif()
else()
	addToCXX("-D NO_GMP")
	message("WARNING: this IntegerType may not be suitable for some input file. Consider using GMP")
endif()

addToCXX("-static-libstdc++")

### 32 bits
option(32BITS "Compile for 32 bit architectures" OFF)
if(32BITS)
	addToCXX("-m32")
	set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -m32")
	set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -m32")
endif()

set(CMAKE_BUILD_TYPE Release CACHE STRING "Choose the type of build.")
set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "Release" "StaticRelease" "StaticDebug" "Profile" "DebugProfile")

if(${CMAKE_BUILD_TYPE} MATCHES "^Profile$")
	addToCXX("-DNDEBUG -O3 -pg ")
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^DebugProfile$")
	addToCXX("-O0 -ggdb -DDEBUG -pg ")
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^StaticRelease$")
	addToCXX("-DNDEBUG -O3 ")
	set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -DNDEBUG ")
	set(BUILD_SHARED_LIBS OFF)
	set(BUILD_MINISATID_STATIC ON)
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^Release$")
	addToCXX("-O3 -DNDEBUG ")
	set(BUILD_SHARED_LIBS ON)
	handleRPATHUnix()
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^StaticDebug$")
	addToCXX("-O0 -ggdb -DDEBUG -D_GLIBCXX_DEBUG ")
	set(BUILD_SHARED_LIBS OFF) # to allow stepping
	set(BUILD_IDP_STATIC ON)   # to allow stepping
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^Debug$")
	addToCXX("-O0 -ggdb -DDEBUG -D_GLIBCXX_DEBUG ")
	set(BUILD_SHARED_LIBS ON)
	handleRPATHUnix()
endif()

MESSAGE(STATUS "build minisatid shared ${BUILD_SHARED_LIBS}")
if(BUILD_MINISATID_STATIC)
	MESSAGE(STATUS "build minisatid allstatic")
endif()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D MINISATIDGITHASH=\\\"${minisatid_git_hash}\\\" ")

MESSAGE(STATUS "MinisatID CXX flags: ")
MESSAGE(STATUS "${CMAKE_CXX_FLAGS}")

add_subdirectory(lib/pbsolver)
if(BUILDTESTS)
	add_subdirectory(lib/gtest-1.6.0)
endif()
add_subdirectory(src)
add_subdirectory(tests)

#Allow packing
set(CPACK_RESOURCE_FILE_LICENSE "${PROJECT_SOURCE_DIR}/COPYING.LESSER")
set(CPACK_PACKAGE_VERSION_MAJOR	${MinisatID_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${MinisatID_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${MinisatID_VERSION_PATCH})
set(CPACK_NSIS_MODIFY_PATH ON)
set(CPACK_SOURCE_GENERATOR TGZ)
# The following components are regex's to match anywhere (unless anchored)
# in absolute path + filename to find files or directories to be excluded
# from source tarball.
# note: escape char is \\\\
set(CPACK_SOURCE_IGNORE_FILES
	"^${PROJECT_SOURCE_DIR}/\\\\..*"
	".*/.git/"
	"^${PROJECT_SOURCE_DIR}/builds/"
	"^${PROJECT_SOURCE_DIR}/build/"
)
message(STATUS "minisatid project source dir: ${PROJECT_SOURCE_DIR}")
message(STATUS "source package name: ${CPACK_SOURCE_PACKAGE_FILE_NAME}")
message(STATUS "source package ignores: ${CPACK_SOURCE_IGNORE_FILES}")
include(CPack)
