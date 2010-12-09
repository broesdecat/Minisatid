AM_CXXFLAGS = @AC_CXXFLAGS@
AM_LDFLAGS = @AC_LDFLAGS@

minisatiddir = $(builddir)
minisatid_DATA = P1.TXT

lib_LTLIBRARIES = libpbsolver.la

#PBSOLVER
include_HEADERS =
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

libpbsolver_la_SOURCES =
libpbsolver_la_SOURCES += pbsolver/Main.C
libpbsolver_la_SOURCES += pbsolver/Debug.C pbsolver/Hardware_adders.C pbsolver/Hardware_clausify.C 
libpbsolver_la_SOURCES += pbsolver/Hardware_sorters.C pbsolver/MiniSat.C pbsolver/PbParser.C
libpbsolver_la_SOURCES += pbsolver/PbSolver.C pbsolver/PbSolver_convertAdd.C pbsolver/PbSolver_convertBdd.C pbsolver/PbSolver_convert.C 
libpbsolver_la_SOURCES += pbsolver/PbSolver_convertSort.C pbsolver/SatELite.C
libpbsolver_la_SOURCES += pbsolver/ADTs/FEnv.C pbsolver/ADTs/File.C pbsolver/ADTs/Global.C pbsolver/pbbase/src/ForwardSearch.cpp
libpbsolver_la_SOURCES += pbsolver/pbbase/src/BNB_oddEven_Cost.cpp pbsolver/pbbase/src/BNB_Comp_Cost.cpp pbsolver/pbbase/src/BNB_SOD_Carry_Cost.cpp  
libpbsolver_la_SOURCES += pbsolver/pbbase/src/GenralBaseFunctions.cpp pbsolver/pbbase/src/MiniSatOrig.cpp pbsolver/pbbase/src/RelativeBaseSearch.cpp 
libpbsolver_la_SOURCES += pbsolver/pbbase/src/SearchMetaData.cpp pbsolver/pbbase/src/THeapComp.cpp pbsolver/pbbase/src/THeap.cpp

AM_CXXFLAGS += -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS
AM_CXXFLAGS += -I$(srcdir)/pbsolver/ -I$(srcdir)/pbsolver/ADTs/ -I$(srcdir)/pbsolver/pbbase/h/ -I$(srcdir)/pbsolver/pbbase/src/