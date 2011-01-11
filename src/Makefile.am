SUBDIRS = pbsolver external mtlold solver3 solver3minisat solver3minisat22 satsolver parser modules theorysolvers utils

AM_CXXFLAGS = @AC_CXXFLAGS@ -I $(top_srcdir)/tclap/include/ #-std=gnu++0x 
AM_LDFLAGS = @AC_LDFLAGS@ #-ltcmalloc -lprofiler

AM_YFLAGS = -d 
AM_LFLAGS =

#ESSENTIAL FOR INTTYPES USAGE 
AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS

bin_PROGRAMS = minisatid

BUILT_SOURCES = parser/ecnfparser.h

minisatid_LDADD = -L$(builddir)/pbsolver -lpbsolver-1.0

minisatid_SOURCES = \
		Main.cpp \
		satsolver/SATSolver.cpp satsolver/SATUtils.cpp\
		parser/ecnftoken.lpp parser/ecnfparser.ypp\
		theorysolvers/PCSolver.cpp theorysolvers/SOSolver.cpp\
		modules/DPLLTmodule.cpp modules/IDSolver.cpp modules/AggSolver.cpp modules/ModSolver.cpp\
		modules/aggsolver/AggTransform.cpp modules/aggsolver/AggUtils.cpp modules/aggsolver/AggPrint.cpp\
		modules/aggsolver/FullyWatched.cpp\
		modules/aggsolver/GenPartiallyWatched.cpp\
		modules/aggsolver/AggProp.cpp\
		external/ExternalInterface.cpp external/ExternalUtils.cpp\
		utils/Print.cpp utils/Utils.cpp utils/PrintMessage.cpp \
		parser/ResourceManager.cpp parser/Lparseread.cpp parser/PBread.cpp parser/ParseOptions.cpp\
		Unittests.cpp\
		satsolver/SATSolver.hpp satsolver/SATUtils.hpp\
		modules/DPLLTmodule.hpp modules/IDSolver.hpp modules/AggSolver.hpp modules/ModSolver.hpp\
		modules/aggsolver/AggTransform.hpp modules/aggsolver/AggUtils.hpp\
		modules/aggsolver/AggPrint.hpp modules/aggsolver/FullyWatched.hpp\
		modules/aggsolver/PartiallyWatched.hpp\
		modules/aggsolver/AggProp.hpp\
		theorysolvers/LogicSolver.hpp theorysolvers/PCSolver.hpp theorysolvers/SOSolver.hpp\
		external/ExternalInterface.hpp external/ExternalUtils.hpp\
		utils/Print.hpp utils/Utils.hpp utils/PrintMessage.hpp utils/IntTypes.h\
		parser/ResourceManager.hpp parser/Lparseread.hpp parser/PBread.hpp\
		parser/ParseOptions.hpp\
		tclap/CmdLine.h\
		external/Translator.hpp external/Translator.cpp\
		Unittests.hpp

#PBSOLVER
minisatid_SOURCES += pbsolver/PbSolver.h
AM_CXXFLAGS += -I$(srcdir)/pbsolver/ -I$(srcdir)/pbsolver/pbbase/h/ -I$(srcdir)/pbsolver/ADTs/


#MINISAT 2.07 09z
if USEMINISAT09Z
minisatid_SOURCES +=\
		solver3/Solver.cpp\
		solver3/Solver.hpp solver3/SolverTypes.hpp\
		mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
AM_CXXFLAGS+= -D USEMINISAT09Z
endif


#MINISAT 2.2
if USEMINISAT22
minisatid_SOURCES +=\
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
minisatid_SOURCES +=\
		solver3minisat/Solver.C\
		solver3minisat/Solver.h solver3minisat/SolverTypes.h\
		mtlold/Vec.h mtlold/Queue.h mtlold/Alg.h mtlold/Heap.h mtlold/Map.h mtlold/Sort.h
AM_CXXFLAGS+= -D USEMINISAT
endif
