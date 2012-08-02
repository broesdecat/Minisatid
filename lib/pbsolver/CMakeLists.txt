cmake_minimum_required (VERSION 2.6)
project (pbsolver)

macro(addToCXX ARGUMENT)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${ARGUMENT}")
endmacro()

addToCXX("-Wno-long-long -Wno-unused-parameter -Wno-unused-result -Wno-strict-aliasing -Wno-vla -Wno-parentheses -Wno-return-type -Wno-variadic-macros")

add_library(pbsolver PBOptions.C
		Hardware_adders.C Hardware_clausify.C
		Hardware_sorters.C MiniSat.C
		PbSolver.C PbSolver_convertAdd.C PbSolver_convertBdd.C PbSolver_convert.C
		PbSolver_convertSort.C
		ADTs/FEnv.C ADTs/File.C ADTs/Global.C pbbase/src/ForwardSearch.cpp
		pbbase/src/BNB_oddEven_Cost.cpp pbbase/src/BNB_Comp_Cost.cpp pbbase/src/BNB_SOD_Carry_Cost.cpp
		pbbase/src/GenralBaseFunctions.cpp pbbase/src/MiniSatOrig.cpp pbbase/src/RelativeBaseSearch.cpp
		pbbase/src/SearchMetaData.cpp pbbase/src/THeapComp.cpp pbbase/src/THeap.cpp
		PBOptions.h Hardware.h 
		MiniSat.h
		PbSolver.h SolverTypes.h VarOrder.h
		ADTs/FEnv.h ADTs/File.h ADTs/Global.h ADTs/Hash_standard.h
		ADTs/Heap.h ADTs/Int.h ADTs/Map.h ADTs/Sort.h ADTs/StackAlloc.h
		ADTs/VecAlloc.h ADTs/VecMaps.h
		pbbase/h/BaseSearchState.h pbbase/h/BaseSearchStateRelativeComp.h
		pbbase/h/BNB_Comp_Cost.h pbbase/h/BNB_oddEven_Cost.h
		pbbase/h/BNB_SOD_Carry_Cost.h pbbase/h/ForwardSearch.h pbbase/h/GenralBaseFunctions.h
		pbbase/h/MiniSatOrig.h pbbase/h/RelativeBaseSearch.h pbbase/h/SearchMetaData.h
		pbbase/h/THeap.h pbbase/h/THeapComp.h)

# add the binary tree to the search path for include files
include_directories ("${PROJECT_BINARY_DIR}")
include_directories ("${PROJECT_SOURCE_DIR}/ADTs" "${PROJECT_SOURCE_DIR}/pbbase/h" "${PROJECT_SOURCE_DIR}")

# add the install targets
install (TARGETS pbsolver DESTINATION lib)
install (FILES "${PROJECT_SOURCE_DIR}/P1.TXT" DESTINATION var/minisatid)
