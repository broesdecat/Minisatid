function(assureOutOfSourceBuilds)
	# make sure the user doesn't play dirty with symlinks
	get_filename_component(srcdir "${CMAKE_SOURCE_DIR}" REALPATH)
	get_filename_component(bindir "${CMAKE_BINARY_DIR}" REALPATH)

	# disallow in-source builds
	if(${srcdir} STREQUAL ${bindir})
		message("######################################################")
		message("You are attempting to build in your Source Directory.")
		message("You must run cmake from a build directory.")
		message("######################################################")

		# attempt to remove cache and cache files... this actually fails to work,
		# but no hurt trying incase it starts working..
		file(REMOVE_RECURSE "${CMAKE_SOURCE_DIR}/CMakeCache.txt" "${CMAKE_SOURCE_DIR}/CMakeFiles")

		message(FATAL_ERROR "In-source builds are forbidden!")
	endif()
	
	# check for polluted source tree
	if(EXISTS ${CMAKE_SOURCE_DIR}/CMakeCache.txt OR EXISTS ${CMAKE_SOURCE_DIR}/CMakeFiles)
		message("######################################################")
		message( "Found results from an in-source build in your source directory.")
		message("######################################################")
	
		# attempt to remove cache and cache files...
		file(REMOVE_RECURSE "${CMAKE_SOURCE_DIR}/CMakeCache.txt" "${CMAKE_SOURCE_DIR}/CMakeFiles")
	
		message(FATAL_ERROR "Source Directory Cleaned, please rerun CMake.")
	endif()
endfunction()