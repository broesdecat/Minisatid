#------------------------------------------------------------------------------
# Copyright (c) 2009, 2010, 2011, Broes De Cat, K.U. Leuven, Belgium
#
# This file is part of MinisatID.
#
# MinisatID is free software: you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# MinisatID is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with MinisatID. If not, see <http://www.gnu.org/licenses/>.
#------------------------------------------------------------------------------

SUBDIRS = parser

LIBSDIR = $(srcdir)/../lib/

AM_CXXFLAGS = @AC_CXXFLAGS@ -I $(LIBSDIR)/tclap/include/ #-std=gnu++0x 
AM_LDFLAGS = @AC_LDFLAGS@ -pthread

AM_YFLAGS = -d 
AM_LFLAGS =

#ESSENTIAL FOR INTTYPES USAGE 
AM_CXXFLAGS+= -D __STDC_FORMAT_MACROS -D __STDC_LIMIT_MACROS

bin_PROGRAMS = minisatid

BUILT_SOURCES = parser/ecnfparser.h

minisatid_LDADD = ../lib/pbsolver/libpbsolver-1.0.la # do not forget ldconfig after installing ;)

if USEPERFTOOLS
minisatid_LDADD += ../lib/perftools/libtcmalloc_minimal.a # -lprofiler
endif

minisatid_SOURCES = \
		Main.cpp \
		parser/ecnftoken.lpp 				parser/ecnfparser.ypp\
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
		external/ExternalInterface.hpp 		external/ExternalInterface.cpp\
		external/ExternalUtils.hpp 			external/ExternalUtils.cpp\
		external/Translator.hpp 			external/Translator.cpp\
		external/InterfaceImpl.hpp 			external/InterfaceImpl.cpp\
		GeneralUtils.hpp 					GeneralUtils.cpp\
		Unittests.hpp 						Unittests.cpp

#PBSOLVER		
AM_CXXFLAGS += -I $(LIBSDIR)/pbsolver/ -I $(LIBSDIR)/pbsolver/pbbase/h/ -I $(LIBSDIR)/pbsolver/ADTs/ -DDATADIR=\"$(datadir)\"

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
