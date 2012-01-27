cmake_minimum_required(VERSION 2.8)

include_directories ("${PROJECT_SOURCE_DIR}/src/")
include_directories ("${PROJECT_SOURCE_DIR}/lib/pluscallback1.7/")
include_directories ("${PROJECT_SOURCE_DIR}/lib/tclap/include")

include_directories (
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/ADTs" 
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/pbbase/h" 
	"${PROJECT_SOURCE_DIR}/lib/pbsolver/"
) 

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D VERSION=\\\"${MinisatID_VERSION_MAJOR}-${MinisatID_VERSION_MINOR}\\\"")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D DATADIR=\"\\\"${CMAKE_INSTALL_PREFIX}/var/minisatid\\\"\"")

if(SOLVER_22)
	set(SATSOLVER_SOURCES satsolver/minisat2-2/minisat/core/Solver.cc
			satsolver/minisat2-2/minisat/core/Solver.h satsolver/minisat2-2/minisat/core/SolverTypes.h 
			satsolver/minisat2-2/minisat/mtl/IntTypes.h satsolver/minisat2-2/minisat/mtl/Alg.h satsolver/minisat2-2/minisat/mtl/Vec.h
			satsolver/minisat2-2/minisat/mtl/Map.h satsolver/minisat2-2/minisat/mtl/Alloc.h
			satsolver/minisat2-2/minisat/mtl/Queue.h satsolver/minisat2-2/minisat/mtl/Heap.h
			satsolver/minisat2-2/minisat/mtl/Sort.h satsolver/minisat2-2/minisat/mtl/XAlloc.h
			satsolver/minisat2-2/minisat/utils/ParseUtils.h satsolver/minisat2-2/minisat/utils/Options.h
	)
	include_directories("${PROJECT_SOURCE_DIR}/src/satsolver/minisat2-2/minisat" "${PROJECT_SOURCE_DIR}/src/satsolver/minisat2-2/")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS -D USEMINISAT22")
endif()

if(SOLVER_214_HACK)
	set(SATSOLVER_SOURCES 
			satsolver/minisat2-14-hack2009/Solver.cpp
			satsolver/minisat2-14-hack2009/Solver.hpp satsolver/minisat2-14-hack2009/SolverTypes.hpp
			satsolver/minisat2-14-hack2009/mtl/Vec.h satsolver/minisat2-14-hack2009/mtl/Queue.h
			satsolver/minisat2-14-hack2009/mtl/Alg.h satsolver/minisat2-14-hack2009/mtl/Heap.h
			satsolver/minisat2-14-hack2009/mtl/Map.h satsolver/minisat2-14-hack2009/mtl/Sort.h
	)
	include_directories("${PROJECT_SOURCE_DIR}/src/satsolver/minisat2-14-hack2009/")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D USEMINISAT09Z ")
endif()

if(USEMINISAT)
	set(SATSOLVER_SOURCES 
			satsolver/minisat2-14/Solver.cpp
			satsolver/minisat2-14/Solver.hpp satsolver/minisat2-14/SolverTypes.hpp
			satsolver/minisat2-14/mtl/Vec.h satsolver/minisat2-14/mtl/Queue.h satsolver/minisat2-14/mtl/Alg.h
			satsolver/minisat2-14/mtl/Heap.h satsolver/minisat2-14/mtl/Map.h satsolver/minisat2-14/mtl/Sort.h
	)
	include_directories("${PROJECT_SOURCE_DIR}/src/satsolver/minisat2-14/")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D USEMINISAT ")
endif()

# CP interface
if(WITHCP)
	set(CP_SOURCES
			modules/CPSolver.hpp 				modules/CPSolver.cpp
			modules/cpsolver/Constraint.hpp		modules/cpsolver/Constraint.cpp
			modules/cpsolver/CPSolverData.hpp	modules/cpsolver/CPSolverData.cpp
			modules/cpsolver/CPUtils.hpp		modules/cpsolver/CPUtils.cpp
			modules/cpsolver/CPScript.hpp		modules/cpsolver/CPScript.cpp
	)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D CPSUPPORT")
endif()

add_library(minisatid
		external/SolvingMonitor.hpp
		external/ResourceManager.hpp
		external/ExternalInterface.hpp		wrapper/ExternalInterface.cpp
		external/Weight.hpp
		external/Idpexception.hpp
		external/Datastructures.hpp
		external/ExternalUtils.hpp
		external/SearchMonitor.hpp
		external/FlatZincRewriter.hpp
		external/Translator.hpp
		external/LazyClauseSupport.hpp
		external/TerminationManagement.hpp
		wrapper/TerminationManagement.cpp
		wrapper/Translator.cpp
		wrapper/FlatZincRewriter.cpp
		wrapper/InterfaceImpl.hpp			wrapper/InterfaceImpl.cpp
		wrapper/SolvingMonitor.cpp
		wrapper/ResourceManager.cpp
		satsolver/SATSolver.hpp				satsolver/SATSolver.cpp
		satsolver/SATUtils.hpp				satsolver/SATUtils.cpp
		modules/DPLLTmodule.hpp 			modules/DPLLTmodule.cpp
		modules/ModSolver.hpp	 			modules/ModSolver.cpp
		modules/IDSolver.hpp 				modules/IDSolver.cpp
		modules/IntVar.hpp 					modules/IntVar.cpp
		modules/BinConstr.hpp 				modules/BinConstr.cpp
		modules/SCCtoCNF.hpp
		modules/aggsolver/AggTransform.hpp 	modules/aggsolver/AggTransform.cpp
		modules/aggsolver/AggUtils.hpp 		modules/aggsolver/AggUtils.cpp
		modules/aggsolver/AggSet.hpp 		modules/aggsolver/AggSet.cpp
		modules/aggsolver/Agg2SAT.hpp
		modules/aggsolver/AggPrint.hpp 		modules/aggsolver/AggPrint.cpp
		modules/aggsolver/FullyWatched.hpp 	modules/aggsolver/FullyWatched.cpp
		modules/aggsolver/PartiallyWatched.hpp modules/aggsolver/PartiallyWatched.cpp
		modules/aggsolver/AggProp.hpp 		modules/aggsolver/AggProp.cpp
		modules/LazyGrounder.hpp	 		modules/LazyGrounder.cpp
		modules/Symmetrymodule.hpp
		theorysolvers/LogicSolver.hpp		theorysolvers/LogicSolver.cpp
		theorysolvers/PCSolver.hpp 			theorysolvers/PCSolver.cpp
		theorysolvers/SOSolver.hpp 			theorysolvers/SOSolver.cpp
		theorysolvers/EventQueue.hpp 		theorysolvers/EventQueue.cpp
		theorysolvers/TimeTrail.hpp
		theorysolvers/PropagatorFactory.hpp theorysolvers/PropagatorFactory.cpp
		utils/IntTypes.h
		utils/Print.hpp 					utils/Print.cpp
		utils/Utils.hpp 					utils/Utils.cpp
		utils/PrintMessage.hpp 				utils/PrintMessage.cpp
		parser/Lparseread.hpp 				parser/Lparseread.cpp
		parser/PBread.hpp 					parser/PBread.cpp
		parser/ParseOptions.hpp 			parser/ParseOptions.cpp
		parser/parsingmonitors/ECNFGraphPrinter.hpp
		parser/parsingmonitors/HumanReadableParsingPrinter.hpp
		parser/parsingmonitors/ParsingMonitor.hpp
		GeneralUtils.hpp 					GeneralUtils.cpp
		Unittests.hpp 						Unittests.cpp
		${SATSOLVER_SOURCES}
		${CP_SOURCES}
)

set(LIBS ${LIBS} pbsolver)

target_link_libraries(minisatid ${LIBS})

find_package(BISON)
find_package(FLEX)

BISON_TARGET(myparser parser/ecnfparser.ypp ${CMAKE_CURRENT_BINARY_DIR}/parser.cc)
FLEX_TARGET(myscanner parser/ecnftoken.lpp  ${CMAKE_CURRENT_BINARY_DIR}/lexer.cc)
ADD_FLEX_BISON_DEPENDENCY(myscanner myparser)

add_executable(minisatid-bin Main.cpp ${BISON_myparser_OUTPUTS} ${FLEX_myscanner_OUTPUTS})
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

MESSAGE(STATUS "Options:")
MESSAGE(STATUS "use22 ${SOLVER_22}")
MESSAGE(STATUS "use2-14 ${SOLVER_214}")
MESSAGE(STATUS "use2-14-hack ${SOLVER_214_HACK}")
MESSAGE(STATUS "use cpsupport ${CPSUPPORT}")
		
#EXTRA_DIST += satsolver/minisat2-2/README satsolver/minisat2-2/LICENSE satsolver/minisat2-2/doc
