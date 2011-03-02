# Copyright 2007-2011 Katholieke Universiteit Leuven
# Use of this software is governed by the GNU LGPLv3.0 license
# Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
# Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
SUBDIRS = parser

LIBSDIR = $(srcdir)/../lib/

AM_CXXFLAGS = @AC_CXXFLAGS@ -I $(LIBSDIR)/tclap/include/ #-std=gnu++0x 
AM_LDFLAGS = @AC_LDFLAGS@ -pthread

AM_YFLAGS = -d 
AM_LFLAGS =

#ESSENTIAL FOR INTTYPES USAGE
AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS

lib_LTLIBRARIES = libminisatid-2.0.la
libminisatid_2_0_la_LDFLAGS = -version-info 1:2:0
minisatid_includedir = $(includedir)/minisatid-2.0

libminisatid_2_0_la_LIBADD = ../lib/pbsolver/libpbsolver-1.0.la # do not forget ldconfig after installing ;)

if USEPERFTOOLS
libminisatid_2_0_la_LIBADD += ../lib/perftools/.libs/libtcmalloc.la ../lib/perftools/.libs/libprofiler.la
endif

bin_PROGRAMS = minisatid
BUILT_SOURCES = parser/ecnfparser.h
minisatid_LDADD = ../src/libminisatid-2.0.la

minisatid_SOURCES = \
		Main.cpp\
		parser/ecnftoken.lpp 				parser/ecnfparser.ypp
		
minisatid_include_HEADERS = \
		external/ExternalInterface.hpp\
		external/ExternalUtils.hpp\
		external/Translator.hpp
		
libminisatid_2_0_la_SOURCES = \
		external/ExternalInterface.hpp		external/ExternalInterface.cpp\
		external/ExternalUtils.hpp\
		external/Translator.hpp				external/Translator.cpp\
		external/InterfaceImpl.hpp			external/InterfaceImpl.cpp\
		satsolver/SATSolver.hpp				satsolver/SATSolver.cpp\
		satsolver/SATUtils.hpp				satsolver/SATUtils.cpp\
		modules/DPLLTmodule.hpp 			modules/DPLLTmodule.cpp\
		modules/ModSolver.hpp	 			modules/ModSolver.cpp\
		modules/IDSolver.hpp 				modules/IDSolver.cpp\
		modules/AggSolver.hpp 				modules/AggSolver.cpp\
		modules/aggsolver/AggTransform.hpp 	modules/aggsolver/AggTransform.cpp\
		modules/aggsolver/AggUtils.hpp 		modules/aggsolver/AggUtils.cpp\
		modules/aggsolver/AggPrint.hpp 		modules/aggsolver/AggPrint.cpp\
		modules/aggsolver/FullyWatched.hpp 	modules/aggsolver/FullyWatched.cpp\
		modules/aggsolver/PartiallyWatched.hpp modules/aggsolver/GenPartiallyWatched.cpp\
		modules/aggsolver/AggProp.hpp 		modules/aggsolver/AggProp.cpp\
		theorysolvers/LogicSolver.hpp\
		theorysolvers/PCSolver.hpp 			theorysolvers/PCSolver.cpp\
		theorysolvers/SOSolver.hpp 			theorysolvers/SOSolver.cpp\
		utils/IntTypes.h\
		utils/Print.hpp 					utils/Print.cpp\
		utils/Utils.hpp 					utils/Utils.cpp\
		utils/PrintMessage.hpp 				utils/PrintMessage.cpp\
		parser/ResourceManager.hpp 			parser/ResourceManager.cpp\
		parser/Lparseread.hpp 				parser/Lparseread.cpp\
		parser/PBread.hpp 					parser/PBread.cpp\
		parser/ParseOptions.hpp 			parser/ParseOptions.cpp\
		GeneralUtils.hpp 					GeneralUtils.cpp\
		Unittests.hpp 						Unittests.cpp

#PBSOLVER		
AM_CXXFLAGS += -I $(LIBSDIR)/pbsolver/ -I $(LIBSDIR)/pbsolver/pbbase/h/ -I $(LIBSDIR)/pbsolver/ADTs/ -DDATADIR=\"$(datadir)\"

#MINISAT 2.07 09z
if USEMINISAT09Z
libminisatid_2_0_la_SOURCES +=\
		solver3/Solver.cpp\
		solver3/Solver.hpp solver3/SolverTypes.hpp\
		mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
AM_CXXFLAGS+= -D USEMINISAT09Z
endif

#MINISAT 2.2
if USEMINISAT22
libminisatid_2_0_la_SOURCES +=\
		solver3minisat22/core/Solver.cc\
		solver3minisat22/core/Solver.h solver3minisat22/core/SolverTypes.h \
		solver3minisat22/mtl/IntTypes.h solver3minisat22/mtl/Alg.h solver3minisat22/mtl/Vec.h\
		solver3minisat22/mtl/Map.h solver3minisat22/mtl/Alloc.h\
		solver3minisat22/mtl/Queue.h solver3minisat22/mtl/Heap.h\
		solver3minisat22/mtl/Sort.h solver3minisat22/mtl/XAlloc.h\
		solver3minisat22/utils/ParseUtils.h solver3minisat22/utils/Options.h\
		solver3minisat22/zconf.h solver3minisat22/zlib.h
AM_CXXFLAGS+= -D USEMINISAT22 -I$(srcdir)/solver3minisat22/
#necessary if not used by minisatid itself! AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS 
endif

#MINISAT 2.07
if USEMINISAT
libminisatid_2_0_la_SOURCES +=\
		solver3minisat/Solver.C\
		solver3minisat/Solver.h solver3minisat/SolverTypes.h\
		mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
AM_CXXFLAGS+= -D USEMINISAT
endif
