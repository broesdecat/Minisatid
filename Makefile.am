AM_LDFLAGS = $(SVNDIGEST_LDFLAGS)
AM_CXXFLAGS = $(SVNDIGEST_CXXFLAGS)
CXXFLAGS = @AM_CXXFLAGS@
LDFLAGS = @AM_LDFLAGS@

YFLAGS = -d @AM_YFLAGS@
LFLAGS = @AM_LFLAGS@ #TODO prefix blijkt niet te werken, dus code herschreven om maar 1 parser te ondersteunen

bin_PROGRAMS = minisatid

BUILT_SOURCES = ecnfparser.h

minisatid_SOURCES = 
minisatid_SOURCES += solvers/Main.cpp solver3/Solver.cpp solvers/IDSolver.cpp solvers/ecnftoken.lpp solvers/ecnfparser.ypp
minisatid_SOURCES += solvers/ModSolver.cpp solvers/PCSolver.cpp solvers/SOSolverHier.cpp solvers/Utils.cpp solvers/aggs/Agg.cpp 
minisatid_SOURCES += solvers/aggs/AggSets.cpp solvers/aggs/AggSolver.cpp solvers/aggs/AggTypes.cpp

include_HEADERS = 
include_HEADERS += solver3/Solver.hpp solver3/SolverTypes.hpp solvers/debug.hpp solvers/IDSolver.hpp solvers/ModSolver.hpp
include_HEADERS += solvers/PCSolver.hpp solvers/solverfwd.hpp solvers/SolverI.hpp solvers/SOSolverHier.hpp solvers/Utils.hpp 
include_HEADERS += solvers/aggs/Agg.hpp solvers/aggs/AggSets.hpp solvers/aggs/AggSolver.hpp solvers/aggs/AggTypes.hpp 
include_HEADERS += mtl/Vec.h mtl/Queue.h mtl/Alg.h mtl/Heap.h mtl/Map.h mtl/Sort.h
dist_doc_DATA = README
