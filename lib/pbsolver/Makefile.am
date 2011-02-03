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

AM_CXXFLAGS = @AC_CXXFLAGS@ -I$(srcdir)/ADTs/ -I$(srcdir)/ -I$(srcdir)/pbbase/h/
AM_LDFLAGS = @AC_LDFLAGS@

lib_LTLIBRARIES = libpbsolver-1.0.la
libpbsolver_1_0_la_LDFLAGS = -version-info 1:2:0
pbsolver_includedir = $(includedir)/pbsolver-1.0

libpbsolver_1_0_la_SOURCES = Main.C \
				Debug.C Hardware_adders.C Hardware_clausify.C \
				Hardware_sorters.C MiniSat.C PbParser.C\
				PbSolver.C PbSolver_convertAdd.C PbSolver_convertBdd.C PbSolver_convert.C \
				PbSolver_convertSort.C SatELite.C\
				ADTs/FEnv.C ADTs/File.C ADTs/Global.C pbbase/src/ForwardSearch.cpp\
				pbbase/src/BNB_oddEven_Cost.cpp pbbase/src/BNB_Comp_Cost.cpp pbbase/src/BNB_SOD_Carry_Cost.cpp  \
				pbbase/src/GenralBaseFunctions.cpp pbbase/src/MiniSatOrig.cpp pbbase/src/RelativeBaseSearch.cpp\
				pbbase/src/SearchMetaData.cpp pbbase/src/THeapComp.cpp pbbase/src/THeap.cpp\
				Main.h Hardware.h \
				Debug.h DebugSolver.h MiniSat.h PbParser.h \
				PbSolver.h SatELite.h Solver.h SolverTypes.h VarOrder.h\
				ADTs/FEnv.h ADTs/File.h ADTs/Global.h ADTs/Hash_standard.h\
				ADTs/Heap.h ADTs/Int.h ADTs/Map.h ADTs/Sort.h ADTs/StackAlloc.h \
				ADTs/VecAlloc.h ADTs/VecMaps.h\
				pbbase/h/BaseSearchState.h pbbase/h/BaseSearchStateRelativeComp.h \
				pbbase/h/BNB_Comp_Cost.h pbbase/h/BNB_oddEven_Cost.h\
				pbbase/h/BNB_SOD_Carry_Cost.h pbbase/h/ForwardSearch.h pbbase/h/GenralBaseFunctions.h \
				pbbase/h/MiniSatOrig.h pbbase/h/RelativeBaseSearch.h pbbase/h/SearchMetaData.h\
				pbbase/h/THeap.h pbbase/h/THeapComp.h
				
pbsolver_include_HEADERS = PbSolver.h

data_pbdir = $(datadir)
dist_data_pb_DATA = P1.TXT