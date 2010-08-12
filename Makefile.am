AM_CPPFLAGS = -I$(srcdir)/solver3minisat22/

YFLAGS = -d 
LFLAGS = #TODO prefix blijkt niet te werken, dus code herschreven om maar 1 parser te ondersteunen

bin_PROGRAMS = minisatid

BUILT_SOURCES = solvers/parser/ecnfparser.h

minisatid_SOURCES = 
minisatid_SOURCES += solvers/Main.cpp solvers/SATUtils.cpp
minisatid_SOURCES += solvers/parser/ecnftoken.lpp solvers/parser/ecnfparser.ypp
minisatid_SOURCES += solvers/pcsolver/PCSolver.cpp 
minisatid_SOURCES += solvers/idsolver/IDSolver.cpp
minisatid_SOURCES += solvers/aggsolver/AggSets.cpp solvers/aggsolver/AggSolver.cpp solvers/aggsolver/Agg.cpp
minisatid_SOURCES += solvers/modsolver/ModSolver.cpp solvers/modsolver/SOSolverHier.cpp
minisatid_SOURCES += solvers/external/ExternalInterface.cpp solvers/external/ExternalUtils.cpp 
minisatid_SOURCES += solvers/utils/Print.cpp solvers/utils/Utils.cpp 
minisatid_SOURCES += solvers/parser/Lparseread.cpp
minisatid_SOURCES += solvers/Unittests.cpp

include_HEADERS = 
include_HEADERS += solvers/utils/Print.hpp solvers/utils/Utils.hpp 
include_HEADERS += solvers/idsolver/IDSolver.hpp
include_HEADERS += solvers/aggsolver/Agg.hpp solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggSets.hpp solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggTypes.hpp 
include_HEADERS += solvers/pcsolver/PCSolver.hpp solvers/pcsolver/ISolver.hpp 
include_HEADERS += solvers/modsolver/ModSolver.hpp solvers/modsolver/SOSolverHier.hpp
include_HEADERS += solvers/external/ExternalInterface.hpp solvers/external/ExternalUtils.hpp
include_HEADERS += solvers/parser/Lparseread.hpp
include_HEADERS += solvers/Unittests.hpp solvers/SolverI.hpp
include_HEADERS += solvers/SATSolver.h solvers/SATUtils.h

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
include_HEADERS += solver3minisat22/mtl/IntTypes.h solver3minisat22/mtl/Alg.h solver3minisat22/mtl/Vec.h solver3minisat22/mtl/Map.h solver3minisat22/mtl/Alloc.h #solver3minisat22/mtl/Vec.h solver3minisat22/mtl/Heap.h solver3minisat22/mtl/Alg.h solver3minisat22/mtl/Sort.h
include_HEADERS += solver3minisat22/utils/ParseUtils.h solver3minisat22/utils/Options.h
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
