# Copyright 2007-2011 Katholieke Universiteit Leuven
# Use of this software is governed by the GNU LGPLv3.0 license
# Written by Broes De Cat and Maarten Mariën, K.U.Leuven, Departement
# Computerwetenschappen, Celestijnenlaan 200A, B-3001 Leuven, Belgium
AM_CXXFLAGS = @AC_CXXFLAGS@ -I$(srcdir)/ADTs/ -I$(srcdir)/ -I$(srcdir)/pbbase/h/
AM_LDFLAGS = @AC_LDFLAGS@ @LIBS@

lib_LTLIBRARIES = libpbsolver-1.0.la
libpbsolver_1_0_la_LDFLAGS = -version-info 1:2:0
pbsolver_includedir = $(includedir)/pbsolver-1.0
libpbsolver_1_0_la_SOURCES = Main.C \
		PB2CNF.hpp PB2CNF.cpp\
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
