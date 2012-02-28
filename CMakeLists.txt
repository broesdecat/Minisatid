cmake_minimum_required(VERSION 2.8)
project (minisatid)

# The version number.
set (MinisatID_VERSION_MAJOR 3)
set (MinisatID_VERSION_MINOR 3)
set (MinisatID_VERSION_PATCH 1)
set (MinisatID_VERSION "${MinisatID_VERSION_MAJOR}.${MinisatID_VERSION_MINOR}.${MinisatID_VERSION_PATCH}")

ENABLE_TESTING()

set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")

### Rpath handling
include(cmake/rpathhandling.cmake)

### Target properties helper
include(cmake/settargetproperties.cmake)

macro(addToCXX ARGUMENT)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${ARGUMENT}")
endmacro()

OPTION(SOLVER_22  		"Use minisat-2-2" ON)
OPTION(SOLVER_214_HACK  "Use minisat-2-14-2009hack" OFF)
OPTION(SOLVER_214  		"Use minisat-2-14" OFF)
OPTION(WITHCP  			"Include cpsupport (need gecode to be installed)" OFF)
set(GECODE_DIR  		"" CACHE STRING "Gecode installation directory (needs include and lib subdirectories)")
OPTION(BUILDTESTS  		"Run the gtest tests" ON)
OPTION(GMP  			"Enable gmp support" OFF)

if(GMP)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D GMP")	
else()
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D NO_GMP")
endif()

if(WITHCP)
	find_package(Gecode)
	if(GECODE_FOUND)
		include_directories(${Gecode_INCLUDE_DIRS})
		set(LIBS ${LIBS} ${Gecode_LIBRARIES})
	else()
		message(FATAL_ERROR "Gecode not found (maybe specify a custom install directory via GECODE_DIR?)")
	endif()
endif()


# Set default compile flags for GCC
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall")
if(CMAKE_COMPILER_IS_GNUCXX)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wextra -pedantic ")
endif()

set(WRONGBUILD ON)
if(${CMAKE_BUILD_TYPE} MATCHES "^Profile")
	addToCXX("-DNDEBUG -O3 -pg ")
	set(WRONGBUILD OFF)
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^StaticRelease")
	addToCXX("-DNDEBUG -O3 -m32 ")
	set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -m32 -DNDEBUG ")
	set(BUILD_SHARED_LIBS OFF)
	set(BUILD_MINISATID_STATIC ON)
	set(WRONGBUILD OFF)
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^Release")
	addToCXX("-O3 -DNDEBUG ")
	set(BUILD_SHARED_LIBS ON)
	handleRPATHUnix()
	set(WRONGBUILD OFF)
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^StaticDebug")
	addToCXX("-O0 -ggdb -DDEBUG -D_GLIBCXX_DEBUG ")
	set(BUILD_SHARED_LIBS OFF) # to allow stepping
	set(BUILD_MINISATID_STATIC ON)   # to allow stepping
	set(WRONGBUILD OFF)
endif()
if(${CMAKE_BUILD_TYPE} MATCHES "^Debug")
	addToCXX("-O0 -ggdb -DDEBUG -D_GLIBCXX_DEBUG ")
	set(BUILD_SHARED_LIBS ON)
	handleRPATHUnix()
	set(WRONGBUILD OFF)
endif()
if(WRONGBUILD)
	message(FATAL_ERROR "Unsupported build-type \"${CMAKE_BUILD_TYPE}\", only Profile, Debug, StaticDebug, Release and StaticRelease are allowed.")
endif()

### RPATH HANDLING
# use, i.e. don't skip the full RPATH for the build tree
SET(CMAKE_SKIP_BUILD_RPATH  FALSE)

# when building, don't use the install RPATH already (but later on when installing)
SET(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE) 
SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")

# add the automatically determined parts of the RPATH which point to directories outside the build tree to the install RPATH
SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)

# the RPATH to be used when installing, but only if it's not a system directory
LIST(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_PREFIX}/lib" isSystemDir)
IF("${isSystemDir}" STREQUAL "-1")
   SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
ENDIF()

MESSAGE(STATUS "build minisatid shared ${BUILD_SHARED_LIBS}")
if(BUILD_MINISATID_STATIC)
	MESSAGE(STATUS "build minisatid allstatic")
endif()

MESSAGE(STATUS "Global CXX flags: ")
MESSAGE(STATUS "${CMAKE_CXX_FLAGS}")

add_subdirectory(lib/pbsolver)
if(BUILDTESTS)
	add_subdirectory(lib/gtest-1.6.0)
endif()
add_subdirectory(src)

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
	"^${PROJECT_SOURCE_DIR}/.git/"
	"^${PROJECT_SOURCE_DIR}/*/.git/"
	"^${PROJECT_SOURCE_DIR}/*/*/.git/"
	"^${PROJECT_SOURCE_DIR}/builds/"
	"^${PROJECT_SOURCE_DIR}/build/"
)
message(STATUS "source package name: ${CPACK_SOURCE_PACKAGE_FILE_NAME}")
message(STATUS "source package ignores: ${CPACK_SOURCE_IGNORE_FILES}")
include(CPack)
