#building with mingw by CXX=pathnaarg++vanmingw

AM_CPPFLAGS = -I$(srcdir)/solver3minisat22/

YFLAGS = -d 
LFLAGS = #TODO prefix blijkt niet te werken, dus code herschreven om maar 1 parser te ondersteunen

bin_PROGRAMS = minisatid

BUILT_SOURCES = solvers/parser/ecnfparser.h

minisatid_SOURCES = 
minisatid_SOURCES += solvers/Main.cpp solvers/SATUtils.cpp
minisatid_SOURCES += solvers/parser/ecnftoken.lpp solvers/parser/ecnfparser.ypp
minisatid_SOURCES += solvers/pcsolver/PCSolver.cpp solvers/pcsolver/SolverModule.cpp 
minisatid_SOURCES += solvers/idsolver/IDSolver.cpp
#minisatid_SOURCES += solvers/aggsolver/AggSets.cpp solvers/aggsolver/AggSolver.cpp solvers/aggsolver/Agg.cpp
minisatid_SOURCES += solvers/aggsolver/AggSolver.cpp solvers/aggsolver/AggComb.cpp solvers/aggsolver/FullyWatched.cpp solvers/aggsolver/PartiallyWatched.cpp solvers/aggsolver/GenPartiallyWatched.cpp
minisatid_SOURCES += solvers/modsolver/ModSolver.cpp solvers/modsolver/SOSolverHier.cpp
minisatid_SOURCES += solvers/external/ExternalInterface.cpp solvers/external/ExternalUtils.cpp 
minisatid_SOURCES += solvers/utils/Print.cpp solvers/utils/Utils.cpp 
minisatid_SOURCES += solvers/parser/Lparseread.cpp
minisatid_SOURCES += solvers/parser/PBread.cpp
#minisatid_SOURCES += solvers/aggsolver/pbsolver/PbSolver.C
minisatid_SOURCES += solvers/Unittests.cpp

include_HEADERS = 
include_HEADERS += solvers/utils/Print.hpp solvers/utils/Utils.hpp 
include_HEADERS += solvers/idsolver/IDSolver.hpp
#include_HEADERS += solvers/aggsolver/Agg.hpp solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggSets.hpp solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggTypes.hpp 
include_HEADERS += solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggComb.hpp solvers/aggsolver/FullyWatched.hpp solvers/aggsolver/PartiallyWatched.hpp
include_HEADERS += solvers/pcsolver/PCSolver.hpp solvers/pcsolver/SolverModule.hpp 
include_HEADERS += solvers/modsolver/ModSolver.hpp solvers/modsolver/SOSolverHier.hpp
include_HEADERS += solvers/external/ExternalInterface.hpp solvers/external/ExternalUtils.hpp
include_HEADERS += solvers/parser/Lparseread.hpp
include_HEADERS += solvers/parser/PBread.hpp
#minisatid_SOURCES += solvers/aggsolver/pbsolver/PbSolver.h solvers/aggsolver/pbsolver/Solver.h
include_HEADERS += solvers/Unittests.hpp solvers/SolverI.hpp
include_HEADERS += solvers/SATSolver.h solvers/SATUtils.h

#PBSOLVER
CXXFLAGS+=-D NO_GMP
include_HEADERS += pbsolver/Main.h
include_HEADERS += pbsolver/Debug.h pbsolver/DebugSolver.h pbsolver/MiniSat.h pbsolver/PbParser.h 
include_HEADERS += pbsolver/PbSolver.h pbsolver/SatELite.h pbsolver/Solver.h pbsolver/SolverTypes.h pbsolver/VarOrder.h
include_HEADERS += pbsolver/ADTs/FEnv.h pbsolver/ADTs/File.h pbsolver/ADTs/Global.h pbsolver/ADTs/Hash_standard.h 
include_HEADERS += pbsolver/ADTs/Heap.h pbsolver/ADTs/Int.h pbsolver/ADTs/Map.h pbsolver/ADTs/Sort.h pbsolver/ADTs/StackAlloc.h 
include_HEADERS += pbsolver/ADTs/VecAlloc.h pbsolver/ADTs/VecMaps.h
include_HEADERS += pbsolver/pbbase/h/BaseSearchState.h pbsolver/pbbase/h/BaseSearchStateRelativeComp.h pbsolver/pbbase/h/BNB_Comp_Cost.h 
include_HEADERS += pbsolver/pbbase/h/BNB_SOD_Carry_Cost.h pbsolver/pbbase/h/ForwardSearch.h pbsolver/pbbase/h/GenralBaseFunctions.h 
include_HEADERS += pbsolver/pbbase/h/MiniSatOrig.h pbsolver/pbbase/h/RelativeBaseSearch.h pbsolver/pbbase/h/SearchMetaData.h 
include_HEADERS += pbsolver/pbbase/h/THeapComp.h pbsolver/pbbase/h/THeap.h

minisatid_SOURCES += pbsolver/Main.C
minisatid_SOURCES += pbsolver/Debug.C pbsolver/Hardware_adders.C pbsolver/Hardware_clausify.C pbsolver/Hardware.h 
minisatid_SOURCES += pbsolver/Hardware_sorters.C pbsolver/MiniSat.C pbsolver/PbParser.C pbsolver/
minisatid_SOURCES += pbsolver/PbSolver.C pbsolver/PbSolver_convertAdd.C pbsolver/PbSolver_convertBdd.C pbsolver/PbSolver_convert.C 
minisatid_SOURCES += pbsolver/PbSolver_convertSort.C pbsolver/SatELite.C
minisatid_SOURCES += pbsolver/ADTs/FEnv.C pbsolver/ADTs/File.C pbsolver/ADTs/Global.C
minisatid_SOURCES += pbsolver/pbbase/src/BNB_Comp_Cost.cpp pbsolver/pbbase/src/BNB_SOD_Carry_Cost.cpp pbsolver/pbbase/src/ForwardSearch.cpp 
minisatid_SOURCES += pbsolver/pbbase/src/GenralBaseFunctions.cpp pbsolver/pbbase/src/MiniSatOrig.cpp pbsolver/pbbase/src/RelativeBaseSearch.cpp 
minisatid_SOURCES += pbsolver/pbbase/src/SearchMetaData.cpp pbsolver/pbbase/src/THeapComp.cpp pbsolver/pbbase/src/THeap.cpp

CXXFLAGS += -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS

#MINISAT 2.07 09z

if USEMINISAT09Z
minisatid_SOURCES += solver3/Solver.cpp 
include_HEADERS += solver3/Solver.hpp solver3/SolverTypes.hpp
include_HEADERS += mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
CXXFLAGS+=-DUSEMINISAT09Z
endif

#MINISAT 2.2
#De -I zorgt ervoor dat ze geladen worden tijdens compileren, de volledige url zorgt ervoor dat ze in de distributie worden gestoken

if USEMINISAT22
minisatid_SOURCES += solver3minisat22/core/Solver.cc
include_HEADERS += solver3minisat22/core/Solver.h solver3minisat22/core/SolverTypes.h
include_HEADERS += solver3minisat22/mtl/IntTypes.h solver3minisat22/mtl/Alg.h solver3minisat22/mtl/Vec.h solver3minisat22/mtl/Map.h solver3minisat22/mtl/Alloc.h
include_HEADERS += solver3minisat22/mtl/Queue.h solver3minisat22/mtl/Heap.h solver3minisat22/mtl/Sort.h solver3minisat22/mtl/XAlloc.h
include_HEADERS += solver3minisat22/utils/ParseUtils.h solver3minisat22/utils/Options.h
include_HEADERS += solver3minisat22/zconf.h solver3minisat22/zlib.h
CXXFLAGS+=-DUSEMINISAT22
endif

#MINISAT 2.07

if USEMINISAT
minisatid_SOURCES += solver3minisat/Solver.C
include_HEADERS += solver3minisat/Solver.h solver3minisat/SolverTypes.h
include_HEADERS += mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
CXXFLAGS+=-DUSEMINISAT
endif

dist_doc_DATA = README
