# Copyright 2007-2011 Katholieke Universiteit Leuven
# Use of this software is governed by the GNU LGPLv3.0 license
# Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
# Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
SUBDIRS = parser

LIBSRCDIR = $(srcdir)/../lib/
LIBBLDDIR = $(builddir)/../lib/

AM_CXXFLAGS = @AC_CXXFLAGS@ -D VERSION=\"$(MINISATID_VERSION)\" -I $(LIBSRCDIR)/tclap/include/ #-std=gnu++0x 
AM_LDFLAGS = @AC_LDFLAGS@

AM_YFLAGS = -d 
AM_LFLAGS =

#ESSENTIAL FOR INTTYPES USAGE
AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS

lib_LTLIBRARIES = libminisatid-2.0.la
libminisatid_2_0_la_LDFLAGS = -version-info 1:0:0
minisatid_includedir = $(includedir)/minisatid-2.0/external

pkgconfigdir = $(libdir)/pkgconfig
pkgconfig_DATA = minisatid-2.0.pc
EXTRA_DIST = minisatid-2.0.pc.in
EXTRA_DIST += satsolver/minisat2-2/README satsolver/minisat2-2/LICENSE satsolver/minisat2-2/doc

libminisatid_2_0_la_LIBADD = @LIBS@ $(LIBBLDDIR)/pbsolver/libpbsolver-1.0.la # do not forget ldconfig after installing ;)

if USEPERFTOOLS
libminisatid_2_0_la_LIBADD += $(LIBBLDDIR)/perftools/.libs/libtcmalloc.la $(LIBBLDDIR)/perftools/.libs/libprofiler.la
endif

bin_PROGRAMS = minisatid
BUILT_SOURCES = parser/ecnfparser.h
minisatid_LDADD = libminisatid-2.0.la

minisatid_SOURCES = \
		Main.cpp\
		parser/ecnftoken.lpp 				parser/ecnfparser.ypp
		
minisatid_include_HEADERS = \
		external/ExternalInterface.hpp\
		external/ExternalUtils.hpp\
		external/Translator.hpp
		
libminisatid_2_0_la_SOURCES = \
		external/ExternalInterface.hpp		wrapper/ExternalInterface.cpp\
		external/ExternalUtils.hpp\
		external/MonitorInterface.hpp\
		external/Translator.hpp				wrapper/Translator.cpp\
		wrapper/InterfaceImpl.hpp			wrapper/InterfaceImpl.cpp\
		external/SolvingMonitor.hpp			wrapper/SolvingMonitor.cpp\
		external/ResourceManager.hpp		wrapper/ResourceManager.cpp\
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
		theorysolvers/LogicSolver.hpp		theorysolvers/LogicSolver.cpp\
		theorysolvers/PCSolver.hpp 			theorysolvers/PCSolver.cpp\
		theorysolvers/SOSolver.hpp 			theorysolvers/SOSolver.cpp\
		utils/IntTypes.h\
		utils/Print.hpp 					utils/Print.cpp\
		utils/ECNFPrinter.hpp				utils/ECNFPrinter.cpp\
		utils/Utils.hpp 					utils/Utils.cpp\
		utils/PrintMessage.hpp 				utils/PrintMessage.cpp\
		parser/Lparseread.hpp 				parser/Lparseread.cpp\
		parser/PBread.hpp 					parser/PBread.cpp\
		parser/ParseOptions.hpp 			parser/ParseOptions.cpp\
		GeneralUtils.hpp 					GeneralUtils.cpp\
		Unittests.hpp 						Unittests.cpp

#PBSOLVER		
AM_CXXFLAGS += -I $(LIBSRCDIR)/pbsolver/ -I $(LIBSRCDIR)/pbsolver/pbbase/h/ -I $(LIBSRCDIR)/pbsolver/ADTs/ -DDATADIR=\"$(datadir)\"

#PLUSCALLBACK
AM_CXXFLAGS += -I $(LIBSDIR)/pluscallback1.7/

#MINISAT 2.07 09z
if USEMINISAT09Z
#m09zdir=satsolver/minisat2-14-hack2009
libminisatid_2_0_la_SOURCES +=\
		satsolver/minisat2-14-hack2009/Solver.cpp\
		satsolver/minisat2-14-hack2009/Solver.hpp satsolver/minisat2-14-hack2009/SolverTypes.hpp\
		satsolver/minisat2-14-hack2009/mtl/Vec.h satsolver/minisat2-14-hack2009/mtl/Queue.h\
		satsolver/minisat2-14-hack2009/mtl/Alg.h satsolver/minisat2-14-hack2009/mtl/Heap.h\
		satsolver/minisat2-14-hack2009/mtl/Map.h satsolver/minisat2-14-hack2009/mtl/Sort.h
AM_CXXFLAGS += -D USEMINISAT09Z -I$(srcdir)/satsolver/minisat2-14-hack2009/
endif

#MINISAT 2.2
if USEMINISAT22
#m22dir=satsolver/minisat2-2/minisat
libminisatid_2_0_la_SOURCES +=\
		satsolver/minisat2-2/minisat/core/Solver.cc\
		satsolver/minisat2-2/minisat/core/Solver.h satsolver/minisat2-2/minisat/core/SolverTypes.h \
		satsolver/minisat2-2/minisat/mtl/IntTypes.h satsolver/minisat2-2/minisat/mtl/Alg.h satsolver/minisat2-2/minisat/mtl/Vec.h\
		satsolver/minisat2-2/minisat/mtl/Map.h satsolver/minisat2-2/minisat/mtl/Alloc.h\
		satsolver/minisat2-2/minisat/mtl/Queue.h satsolver/minisat2-2/minisat/mtl/Heap.h\
		satsolver/minisat2-2/minisat/mtl/Sort.h satsolver/minisat2-2/minisat/mtl/XAlloc.h\
		satsolver/minisat2-2/minisat/utils/ParseUtils.h satsolver/minisat2-2/minisat/utils/Options.h
AM_CXXFLAGS+= -D USEMINISAT22 -I$(srcdir)/satsolver/minisat2-2/minisat -I$(srcdir)/satsolver/minisat2-2/
#add if not added by minisatid itself! AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS
endif

#MINISAT 2.07
if USEMINISAT
#m214dir=satsolver/minisat2-14
libminisatid_2_0_la_SOURCES +=\
		satsolver/minisat2-14/Solver.cpp\
		satsolver/minisat2-14/Solver.hpp satsolver/minisat2-14/SolverTypes.hpp\
		satsolver/minisat2-14/mtl/Vec.h satsolver/minisat2-14/mtl/Queue.h satsolver/minisat2-14/mtl/Alg.h\
		satsolver/minisat2-14/mtl/Heap.h satsolver/minisat2-14/mtl/Map.h satsolver/minisat2-14/mtl/Sort.h
AM_CXXFLAGS += -D USEMINISAT -I$(srcdir)/satsolver/minisat2-14/
endif
