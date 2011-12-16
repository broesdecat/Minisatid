# Copyright 2007-2011 Katholieke Universiteit Leuven
# Use of this software is governed by the GNU LGPLv3.0 license
# Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
# Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
SUBDIRS = parser

libssourcedir = $(srcdir)/../lib/
libsbuilddir = $(builddir)/../lib/

AM_CXXFLAGS = @AC_CXXFLAGS@ -D VERSION=\"$(MINISATID_VERSION)\" -std=c++0x 

lib_LTLIBRARIES = libminisatid-2.0.la
libminisatid_2_0_la_LDFLAGS = -version-info 1:0:0
minisatid_includedir = $(includedir)/minisatid-2.0/external

pkgconfigdir = $(libdir)/pkgconfig
pkgconfig_DATA = minisatid-2.0.pc
EXTRA_DIST = minisatid-2.0.pc.in

# do not forget ldconfig after installing ;)
libminisatid_2_0_la_LIBADD = @minisatliblibs@ $(libsbuilddir)/pbsolver/libpbsolver-1.0.la
	
libminisatid_2_0_la_SOURCES = \
		external/SolvingMonitor.hpp\
		external/ResourceManager.hpp\
		external/ExternalInterface.hpp		wrapper/ExternalInterface.cpp\
		external/Weight.hpp\
		external/Idpexception.hpp\
		external/Datastructures.hpp\
		external/ExternalUtils.hpp\
		external/SearchMonitor.hpp\
		external/FlatZincRewriter.hpp\
		external/Translator.hpp\
		external/LazyClauseSupport.hpp\
		external/TerminationManager.hpp\
		wrapper/TerminationManagement.cpp\
		wrapper/Translator.cpp\
		wrapper/FlatZincRewriter.cpp\
		wrapper/InterfaceImpl.hpp			wrapper/InterfaceImpl.cpp\
		wrapper/SolvingMonitor.cpp\
		wrapper/ResourceManager.cpp\
		satsolver/SATSolver.hpp				satsolver/SATSolver.cpp\
		satsolver/SATUtils.hpp				satsolver/SATUtils.cpp\
		modules/DPLLTmodule.hpp 			modules/DPLLTmodule.cpp\
		modules/ModSolver.hpp	 			modules/ModSolver.cpp\
		modules/IDSolver.hpp 				modules/IDSolver.cpp\
		modules/IntVar.hpp 					modules/IntVar.cpp\
		modules/BinConstr.hpp 				modules/BinConstr.cpp\
		modules/SCCtoCNF.hpp\
		modules/aggsolver/AggTransform.hpp 	modules/aggsolver/AggTransform.cpp\
		modules/aggsolver/AggUtils.hpp 		modules/aggsolver/AggUtils.cpp\
		modules/aggsolver/AggSet.hpp 		modules/aggsolver/AggSet.cpp\
		modules/aggsolver/Agg2SAT.hpp\
		modules/aggsolver/AggPrint.hpp 		modules/aggsolver/AggPrint.cpp\
		modules/aggsolver/FullyWatched.hpp 	modules/aggsolver/FullyWatched.cpp\
		modules/aggsolver/PartiallyWatched.hpp modules/aggsolver/PartiallyWatched.cpp\
		modules/aggsolver/AggProp.hpp 		modules/aggsolver/AggProp.cpp\
		modules/LazyGrounder.hpp	 		modules/LazyGrounder.cpp\
		modules/Symmetrymodule.hpp\
		theorysolvers/LogicSolver.hpp		theorysolvers/LogicSolver.cpp\
		theorysolvers/PCSolver.hpp 			theorysolvers/PCSolver.cpp\
		theorysolvers/SOSolver.hpp 			theorysolvers/SOSolver.cpp\
		theorysolvers/EventQueue.hpp 		theorysolvers/EventQueue.cpp\
		theorysolvers/TimeTrail.hpp\
		theorysolvers/PropagatorFactory.hpp theorysolvers/PropagatorFactory.cpp\
		utils/IntTypes.h\
		utils/Print.hpp 					utils/Print.cpp\
		utils/Utils.hpp 					utils/Utils.cpp\
		utils/PrintMessage.hpp 				utils/PrintMessage.cpp\
		parser/Lparseread.hpp 				parser/Lparseread.cpp\
		parser/PBread.hpp 					parser/PBread.cpp\
		parser/ParseOptions.hpp 			parser/ParseOptions.cpp\
		parser/parsingmonitors/ECNFGraphPrinter.hpp\
		parser/parsingmonitors/HumanReadableParsingPrinter.hpp\
		parser/parsingmonitors/ParsingMonitor.hpp\
		GeneralUtils.hpp 					GeneralUtils.cpp\
		Unittests.hpp 						Unittests.cpp

# TClap argument parsing framework
AM_CXXFLAGS += -I $(libssourcedir)/tclap/include/

# Required for inttypes usage
AM_CXXFLAGS += -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS

# Callback framework
AM_CXXFLAGS += -I $(libssourcedir)/pluscallback1.7/

# Pbsolver		
AM_CXXFLAGS += \
		-I $(libssourcedir)/pbsolver/ -I $(libssourcedir)/pbsolver/pbbase/h/ \
		-I $(libssourcedir)/pbsolver/ADTs/ -DDATADIR=\"$(datadir)\"

# Minisat 2.14 2009z
if USEMINISAT09Z
libminisatid_2_0_la_SOURCES +=\
		satsolver/minisat2-14-hack2009/Solver.cpp\
		satsolver/minisat2-14-hack2009/Solver.hpp satsolver/minisat2-14-hack2009/SolverTypes.hpp\
		satsolver/minisat2-14-hack2009/mtl/Vec.h satsolver/minisat2-14-hack2009/mtl/Queue.h\
		satsolver/minisat2-14-hack2009/mtl/Alg.h satsolver/minisat2-14-hack2009/mtl/Heap.h\
		satsolver/minisat2-14-hack2009/mtl/Map.h satsolver/minisat2-14-hack2009/mtl/Sort.h
AM_CXXFLAGS += -D USEMINISAT09Z -I$(srcdir)/satsolver/minisat2-14-hack2009/
endif

# Minisat 2.2
if USEMINISAT22
libminisatid_2_0_la_SOURCES +=\
		satsolver/minisat2-2/minisat/core/Solver.cc\
		satsolver/minisat2-2/minisat/core/Solver.h satsolver/minisat2-2/minisat/core/SolverTypes.h \
		satsolver/minisat2-2/minisat/mtl/IntTypes.h satsolver/minisat2-2/minisat/mtl/Alg.h satsolver/minisat2-2/minisat/mtl/Vec.h\
		satsolver/minisat2-2/minisat/mtl/Map.h satsolver/minisat2-2/minisat/mtl/Alloc.h\
		satsolver/minisat2-2/minisat/mtl/Queue.h satsolver/minisat2-2/minisat/mtl/Heap.h\
		satsolver/minisat2-2/minisat/mtl/Sort.h satsolver/minisat2-2/minisat/mtl/XAlloc.h\
		satsolver/minisat2-2/minisat/utils/ParseUtils.h satsolver/minisat2-2/minisat/utils/Options.h
AM_CXXFLAGS+= -D USEMINISAT22 -I$(srcdir)/satsolver/minisat2-2/minisat -I$(srcdir)/satsolver/minisat2-2/
#also requires AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS
endif

# Minisat 2.14
if USEMINISAT
libminisatid_2_0_la_SOURCES +=\
		satsolver/minisat2-14/Solver.cpp\
		satsolver/minisat2-14/Solver.hpp satsolver/minisat2-14/SolverTypes.hpp\
		satsolver/minisat2-14/mtl/Vec.h satsolver/minisat2-14/mtl/Queue.h satsolver/minisat2-14/mtl/Alg.h\
		satsolver/minisat2-14/mtl/Heap.h satsolver/minisat2-14/mtl/Map.h satsolver/minisat2-14/mtl/Sort.h
AM_CXXFLAGS += -D USEMINISAT -I$(srcdir)/satsolver/minisat2-14/
endif

# CP interface
if USECPSUPPORT
libminisatid_2_0_la_SOURCES +=\
		modules/CPSolver.hpp 				modules/CPSolver.cpp\
		modules/cpsolver/Constraint.hpp		modules/cpsolver/Constraint.cpp\
		modules/cpsolver/CPSolverData.hpp	modules/cpsolver/CPSolverData.cpp\
		modules/cpsolver/CPUtils.hpp		modules/cpsolver/CPUtils.cpp\
		modules/cpsolver/CPScript.hpp		modules/cpsolver/CPScript.cpp
AM_CXXFLAGS += -D CPSUPPORT
endif

AM_YFLAGS = -d 
AM_LFLAGS =

bin_PROGRAMS = minisatid 
if BUILDTESTS
bin_PROGRAMS += alltests
endif 
BUILT_SOURCES = parser/ecnfparser.h
minisatid_LDADD = libminisatid-2.0.la

minisatid_SOURCES = \
		Main.cpp\
		parser/ecnftoken.lpp 				parser/ecnfparser.ypp
		
EXTRA_DIST += satsolver/minisat2-2/README satsolver/minisat2-2/LICENSE satsolver/minisat2-2/doc
		
minisatid_include_HEADERS = \
		external/ExternalInterface.hpp\
		external/ExternalUtils.hpp\
		external/Translator.hpp

alltests_SOURCES = tests/googletestsnippet.cpp tests/janhunentest.cpp
# below is a workaround which allows to reuse SOURCES and still guarantee unique names (if using it on different targets) 
#alltests_CXXFLAGS = $(AM_CXXFLAGS)
alltests_LDADD = -lgtest -lpthread libminisatid-2.0.la

TESTS = alltests

#issue with google test?
DISTCLEANFILES = alltests 
