AM_LDFLAGS = $(SVNDIGEST_LDFLAGS)
AM_CXXFLAGS = $(SVNDIGEST_CXXFLAGS)
CXXFLAGS = -I/home/broes/documents/othersoftware/gecode/installnostat/include/ @AM_CXXFLAGS@
LDFLAGS = -L/home/broes/documents/othersoftware/gecode/installnostat/lib/ -lgecodedriver -lgecodeminimodel -lgecodeset -lgecodeint -lgecodekernel -lgecodesupport @AM_LDFLAGS@

YFLAGS = -d @AM_YFLAGS@
LFLAGS = @AM_LFLAGS@ #TODO prefix blijkt niet te werken, dus code herschreven om maar 1 parser te ondersteunen

bin_PROGRAMS = minisatid

BUILT_SOURCES = ecnfparser.h

minisatid_SOURCES = 
minisatid_SOURCES += solvers/Main.cpp 
minisatid_SOURCES += solvers/parser/ecnftoken.lpp solvers/parser/ecnfparser.ypp
minisatid_SOURCES += solvers/pcsolver/PCSolver.cpp 
minisatid_SOURCES += solvers/idsolver/IDSolver.cpp
minisatid_SOURCES += solvers/aggsolver/AggSets.cpp solvers/aggsolver/AggSolver.cpp solvers/aggsolver/Agg.cpp
minisatid_SOURCES += solvers/cpsolver/CPSolver.cpp solvers/cpsolver/CPScript.cpp solvers/cpsolver/Constraint.cpp solvers/cpsolver/CPSolverData.cpp
minisatid_SOURCES += solvers/modsolver/ModSolver.cpp solvers/modsolver/SOSolverHier.cpp
minisatid_SOURCES += solvers/external/ExternalInterface.cpp solvers/external/ExternalUtils.cpp 
minisatid_SOURCES += solvers/utils/Print.cpp solvers/utils/Utils.cpp
minisatid_SOURCES += solvers/parser/Lparseread.cpp
minisatid_SOURCES += solvers/Unittests.cpp

include_HEADERS = 
include_HEADERS += solvers/utils/Debug.hpp solvers/utils/Print.hpp solvers/utils/Solverfwd.hpp solvers/SolverI.hpp solvers/utils/Utils.hpp 
include_HEADERS += solvers/idsolver/IDSolver.hpp
include_HEADERS += solvers/aggsolver/Agg.hpp solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggSets.hpp solvers/aggsolver/AggSolver.hpp solvers/aggsolver/AggTypes.hpp 
include_HEADERS += solvers/pcsolver/PCSolver.hpp 
include_HEADERS += solvers/cpsolver/CPUtils.hpp solvers/cpsolver/CPSolver.hpp solvers/cpsolver/CPScript.hpp solvers/cpsolver/Constraint.hpp solvers/cpsolver/CPSolverData.hpp
include_HEADERS += solvers/modsolver/ModSolver.hpp solvers/modsolver/SOSolverHier.hpp
include_HEADERS += solvers/external/ExternalInterface.hpp solvers/external/ExternalUtils.hpp 
include_HEADERS += mtl/Vec.h mtl/Queue.h mtl/Alg.h mtl/Heap.h mtl/Map.h mtl/Sort.h
include_HEADERS += solvers/parser/Lparseread.hpp
include_HEADERS += solvers/Unittests.hpp

#MINISAT 2.07 09z
#minisatid_SOURCES += solver3/Solver.cpp 
#include_HEADERS += solver3/Solver.hpp solver3/SolverTypes.hpp

#MINISAT 2.07
minisatid_SOURCES += solver3minisat/Solver.C
include_HEADERS += solver3minisat/Solver.h solver3minisat/SolverTypes.h

#MINISAT 2.2

dist_doc_DATA = README
