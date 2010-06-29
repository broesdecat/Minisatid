AM_LDFLAGS = $(SVNDIGEST_LDFLAGS)
AM_CXXFLAGS = $(SVNDIGEST_CXXFLAGS)
CXXFLAGS =  -I$(top_srcdir)/mtl -I$(top_srcdir)/solver3 -I$(top_srcdir)/../../othersoftware/gecode/install/include/ @AM_CXXFLAGS@
LDFLAGS = -L$(top_srcdir)/../../othersoftware/gecode/installnostat/lib/ -lgecodedriver -lgecodeminimodel -lgecodeset -lgecodeint -lgecodekernel -lgecodesupport @AM_LDFLAGS@

YFLAGS = -d @AM_YFLAGS@
LFLAGS = @AM_LFLAGS@ #TODO prefix blijkt niet te werken, dus code herschreven om maar 1 parser te ondersteunen

bin_PROGRAMS = minisatid

BUILT_SOURCES = ecnfparser.h

minisatid_SOURCES = 
minisatid_SOURCES += solvers/Main.cpp 
minisatid_SOURCES += solvers/ecnftoken.lpp solvers/ecnfparser.ypp
minisatid_SOURCES += solvers/PCSolver.cpp solvers/Utils.cpp 
minisatid_SOURCES += solver3/Solver.cpp 
minisatid_SOURCES += solvers/IDSolver.cpp
minisatid_SOURCES += solvers/aggs/AggSets.cpp solvers/aggs/AggSolver.cpp solvers/aggs/AggTypes.cpp solvers/aggs/Agg.cpp
minisatid_SOURCES += solvers/CPSolver.cpp
minisatid_SOURCES += solvers/ModSolver.cpp solvers/SOSolverHier.cpp 
minisatid_SOURCES += solvers/Print.cpp

include_HEADERS = 
include_HEADERS += solvers/debug.hpp solvers/Print.hpp solvers/solverfwd.hpp solvers/SolverI.hpp
include_HEADERS += solver3/Solver.hpp solver3/SolverTypes.hpp
include_HEADERS += mtl/Vec.h mtl/Queue.h mtl/Alg.h mtl/Heap.h mtl/Map.h mtl/Sort.h
include_HEADERS += solvers/IDSolver.hpp
include_HEADERS += solvers/aggs/Agg.hpp solvers/aggs/AggSets.hpp solvers/aggs/AggSolver.hpp solvers/aggs/AggTypes.hpp 
include_HEADERS += solvers/PCSolver.hpp solvers/Utils.hpp 
include_HEADERS += solvers/CPSolver.hpp
include_HEADERS += solvers/ModSolver.hpp solvers/SOSolverHier.hpp 
include_HEADERS += gecode/kernel.hh gecode/int.hh gecode/minimodel.hh gecode/driver.hh


dist_doc_DATA = README
dist_doc_DATA += makefilewinmac
