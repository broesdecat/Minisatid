SUBDIRS = tclap

AM_CXXFLAGS = @AC_CXXFLAGS@  -I$(srcdir)/src/
AM_LDFLAGS = @AC_LDFLAGS@  -Itclap/ #-ltcmalloc -lprofiler -lpbsolver

YFLAGS = -d 
LFLAGS = 

bin_PROGRAMS = minisatid

minisatiddir = $(builddir)
minisatid_DATA = P1.TXT

BUILT_SOURCES = parser/ecnfparser.h

minisatid_SOURCES = 
minisatid_SOURCES += Main.cpp 
minisatid_SOURCES += satsolver/SATSolver.cpp satsolver/SATUtils.cpp
minisatid_SOURCES += parser/ecnftoken.lpp parser/ecnfparser.ypp
minisatid_SOURCES += theorysolvers/PCSolver.cpp theorysolvers/SOSolver.cpp
minisatid_SOURCES += modules/DPLLTmodule.cpp modules/IDSolver.cpp modules/AggSolver.cpp modules/ModSolver.cpp
minisatid_SOURCES += modules/aggsolver/AggTransform.cpp modules/aggsolver/AggUtils.cpp modules/aggsolver/AggPrint.cpp modules/aggsolver/FullyWatched.cpp modules/aggsolver/PartiallyWatched.cpp modules/aggsolver/GenPartiallyWatched.cpp
minisatid_SOURCES += modules/aggsolver/AggProp.cpp
minisatid_SOURCES += external/ExternalInterface.cpp external/ExternalUtils.cpp 
minisatid_SOURCES += utils/Print.cpp utils/Utils.cpp utils/PrintMessage.cpp 
minisatid_SOURCES += parser/ResourceManager.cpp parser/Lparseread.cpp parser/PBread.cpp parser/ParseOptions.cpp
minisatid_SOURCES += Unittests.cpp

include_HEADERS = 
include_HEADERS += satsolver/SATSolver.h satsolver/SATUtils.h 
include_HEADERS += modules/DPLLTmodule.hpp modules/IDSolver.hpp modules/AggSolver.hpp modules/ModSolver.hpp
include_HEADERS += modules/aggsolver/AggTransform.hpp modules/aggsolver/AggUtils.hpp modules/aggsolver/AggPrint.hpp modules/aggsolver/FullyWatched.hpp modules/aggsolver/PartiallyWatched.hpp
include_HEADERS += modules/aggsolver/AggProp.hpp
include_HEADERS += theorysolvers/LogicSolver.hpp theorysolvers/PCSolver.hpp theorysolvers/SOSolver.hpp   
include_HEADERS += external/ExternalInterface.hpp external/ExternalUtils.hpp
include_HEADERS += utils/Print.hpp utils/Utils.hpp utils/PrintMessage.hpp
include_HEADERS += parser/ResourceManager.hpp parser/Lparseread.hpp parser/PBread.hpp parser/ParseOptions.hpp tclap/CmdLine.h
include_HEADERS += Unittests.hpp 


#PBSOLVER
include_HEADERS += pbsolver/Main.h pbsolver/Hardware.h 
include_HEADERS += pbsolver/Debug.h pbsolver/DebugSolver.h pbsolver/MiniSat.h pbsolver/PbParser.h 
include_HEADERS += pbsolver/PbSolver.h pbsolver/SatELite.h pbsolver/Solver.h pbsolver/SolverTypes.h pbsolver/VarOrder.h
include_HEADERS += pbsolver/ADTs/FEnv.h pbsolver/ADTs/File.h pbsolver/ADTs/Global.h pbsolver/ADTs/Hash_standard.h 
include_HEADERS += pbsolver/ADTs/Heap.h pbsolver/ADTs/Int.h pbsolver/ADTs/Map.h pbsolver/ADTs/Sort.h pbsolver/ADTs/StackAlloc.h 
include_HEADERS += pbsolver/ADTs/VecAlloc.h pbsolver/ADTs/VecMaps.h
include_HEADERS += pbsolver/pbbase/h/BaseSearchState.h pbsolver/pbbase/h/BaseSearchStateRelativeComp.h pbsolver/pbbase/h/BNB_Comp_Cost.h pbsolver/pbbase/h/BNB_oddEven_Cost.h
include_HEADERS += pbsolver/pbbase/h/BNB_SOD_Carry_Cost.h pbsolver/pbbase/h/ForwardSearch.h pbsolver/pbbase/h/GenralBaseFunctions.h 
include_HEADERS += pbsolver/pbbase/h/MiniSatOrig.h pbsolver/pbbase/h/RelativeBaseSearch.h pbsolver/pbbase/h/SearchMetaData.h 
include_HEADERS += pbsolver/pbbase/h/THeapComp.h pbsolver/pbbase/h/THeap.h

minisatid_SOURCES += pbsolver/Main.C
minisatid_SOURCES += pbsolver/Debug.C pbsolver/Hardware_adders.C pbsolver/Hardware_clausify.C 
minisatid_SOURCES += pbsolver/Hardware_sorters.C pbsolver/MiniSat.C pbsolver/PbParser.C
minisatid_SOURCES += pbsolver/PbSolver.C pbsolver/PbSolver_convertAdd.C pbsolver/PbSolver_convertBdd.C pbsolver/PbSolver_convert.C 
minisatid_SOURCES += pbsolver/PbSolver_convertSort.C pbsolver/SatELite.C
minisatid_SOURCES += pbsolver/ADTs/FEnv.C pbsolver/ADTs/File.C pbsolver/ADTs/Global.C pbsolver/pbbase/src/ForwardSearch.cpp
minisatid_SOURCES += pbsolver/pbbase/src/BNB_oddEven_Cost.cpp pbsolver/pbbase/src/BNB_Comp_Cost.cpp pbsolver/pbbase/src/BNB_SOD_Carry_Cost.cpp  
minisatid_SOURCES += pbsolver/pbbase/src/GenralBaseFunctions.cpp pbsolver/pbbase/src/MiniSatOrig.cpp pbsolver/pbbase/src/RelativeBaseSearch.cpp 
minisatid_SOURCES += pbsolver/pbbase/src/SearchMetaData.cpp pbsolver/pbbase/src/THeapComp.cpp pbsolver/pbbase/src/THeap.cpp

AM_CXXFLAGS += -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
AM_CXXFLAGS += -I$(srcdir)/pbsolver/ -I$(srcdir)/pbsolver/ADTs/ -I$(srcdir)/pbsolver/pbbase/h/ -I$(srcdir)/pbsolver/pbbase/src/


#MINISAT 2.07 09z
if USEMINISAT09Z
minisatid_SOURCES += solver3/Solver.cpp 
include_HEADERS += solver3/Solver.hpp solver3/SolverTypes.hpp
include_HEADERS += mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
AM_CXXFLAGS+=-DUSEMINISAT09Z
endif


#MINISAT 2.2
if USEMINISAT22
minisatid_SOURCES += solver3minisat22/core/Solver.cc
include_HEADERS += solver3minisat22/core/Solver.h solver3minisat22/core/SolverTypes.h
include_HEADERS += solver3minisat22/mtl/IntTypes.h solver3minisat22/mtl/Alg.h solver3minisat22/mtl/Vec.h solver3minisat22/mtl/Map.h solver3minisat22/mtl/Alloc.h
include_HEADERS += solver3minisat22/mtl/Queue.h solver3minisat22/mtl/Heap.h solver3minisat22/mtl/Sort.h solver3minisat22/mtl/XAlloc.h
include_HEADERS += solver3minisat22/utils/ParseUtils.h solver3minisat22/utils/Options.h
include_HEADERS += solver3minisat22/zconf.h solver3minisat22/zlib.h
AM_CXXFLAGS+=-DUSEMINISAT22 -I$(srcdir)/solver3minisat22/
endif

#MINISAT 2.07
if USEMINISAT
minisatid_SOURCES += solver3minisat/Solver.C
include_HEADERS += solver3minisat/Solver.h solver3minisat/SolverTypes.h
include_HEADERS += mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
AM_CXXFLAGS+=-DUSEMINISAT
endif
