# Compiler
CXX=g++
CXXFLAGS= -Wall -Wextra -Wno-unused-parameter -ffloat-store -pedantic -Wno-variadic-macros #-D GMP -mconsole

# Lexer
FLEX=flex
FLEXFLAGS=

# Parser generator
YACC=bison
YACCFLAGS=--defines

# filenames
# ############################################################
PHDRS	= solvers/ecnfparser.h 
CHDRS	= $(PHDRS) solvers/debug.hpp solvers/IDSolver.hpp solvers/ModSolver.hpp 
CHDRS	+= solvers/PCSolver.hpp solvers/solverfwd.hpp solvers/SolverI.hpp solvers/SOSolverHier.hpp solvers/Utils.hpp 
CHDRS	+= solvers/aggs/Agg.hpp solvers/aggs/AggSets.hpp solvers/aggs/AggSolver.hpp solvers/aggs/AggTypes.hpp 
CHDRS	+= mtl/Vec.h mtl/Queue.h mtl/Alg.h mtl/Heap.h mtl/Map.h mtl/Sort.h
CHDRS += solver3/Solver.hpp solver3/SolverTypes.hpp
PSRCS	= solvers/ecnfparser.cpp solvers/ecnftoken.cpp
CSRCS	= $(PSRCS) solvers/Main.cpp solvers/IDSolver.cpp solvers/Main.cpp solvers/ModSolver.cpp solvers/PCSolver.cpp 
CSRCS	+= solvers/SOSolverHier.cpp solvers/Utils.cpp solvers/aggs/Agg.cpp solvers/aggs/AggSets.cpp solvers/aggs/AggSolver.cpp solvers/aggs/AggTypes.cpp
CSRCS += solver3/Solver.cpp 

CXXFLAGS += -Imtl -Isolvers -Isolvers/aggs -Isolver3
LFLAGS	= #-lz -lgmpxx -lgmp
EXEC	= minisatid

EXEC	?= $(notdir $(shell pwd))
LIB		?= $(EXEC)

COBJS	= $(addsuffix .o, $(basename $(CSRCS)))
PCOBJS	= $(addsuffix p,  $(COBJS))
DCOBJS	= $(addsuffix d,  $(COBJS))
RCOBJS	= $(addsuffix r,  $(COBJS))
CCCOBJS	= $(addsuffix cc,  $(COBJS))

# stuff to make
# ############################################################

.PHONY : s cc p d r rs lib libd clean

s:	$(EXEC)	
p:	$(EXEC)_profile
d:	$(EXEC)_debug
r:	$(EXEC)_release
cc: $(EXEC)_codecover
rs:	$(EXEC)_static
lib:	lib$(LIB).a
libd:	lib$(LIB)d.a

COPTIMIZE ?= -O3

## Compile options
$(EXEC):			CXXFLAGS += $(COPTIMIZE) -ggdb -D DEBUG
$(EXEC)_profile:	CXXFLAGS += $(COPTIMIZE) -pg -ggdb -D NDEBUG
$(EXEC)_debug:		CXXFLAGS += -O0 -ggdb -D DEBUG # -D INVARIANTS
$(EXEC)_release:	CXXFLAGS += $(COPTIMIZE) -D NDEBUG
$(EXEC)_static:		CXXFLAGS += $(COPTIMIZE) -D NDEBUG
$(EXEC)_codecover:	CXXFLAGS += -O0 -fprofile-arcs -ftest-coverage -ggdb -D DEBUG # -D INVARIANTS

## Link options
$(EXEC):			LFLAGS += -ggdb
$(EXEC)_profile:	LFLAGS += -ggdb -pg
$(EXEC)_debug:		LFLAGS += -ggdb
$(EXEC)_release:	LFLAGS += 
$(EXEC)_static:		LFLAGS += --static
$(EXEC)_codecover:	LFLAGS += -ggdb -lgcov

## Dependencies
$(EXEC):			$(COBJS)
$(EXEC)_profile:	$(PCOBJS)
$(EXEC)_debug:		$(DCOBJS)
$(EXEC)_release:	$(RCOBJS)
$(EXEC)_static:		$(RCOBJS)
$(EXEC)_codecover:	$(CCCOBJS)

# build rules
# ############################################################
%.o %.op %.od %.or %.occ: %.cpp
	@echo Compiling: "$@ ( $< )"
	@$(CXX) $(CXXFLAGS) -c -o $@ $<
	
%/ecnfparser.cpp: %/ecnfparser.ypp
	@echo Compiling: "$@ ( $< )"
	@$(YACC) $(YACCFLAGS) --output=$@ $< #-p ecnf 
	
%/ecnftoken.cpp: %/ecnftoken.lpp
	@echo Compiling: "$@ ( $< )"
	@$(FLEX) $(FLEXFLAGS) -o$@ $< #-P ecnf

$(EXEC) $(EXEC)_codecover $(EXEC)_profile $(EXEC)_debug $(EXEC)_release $(EXEC)_static:
	@echo Linking: "$@ ( $^ )"
	@$(CXX) $^ $(CXXFLAGS) $(LFLAGS) -o $@

clean:
	@rm -f $(EXEC) $(EXEC)_codecover $(EXEC)_profile $(EXEC)_debug $(EXEC)_release $(EXEC)_static $(PSRCS) $(PHDRS) $(COBJS) $(PCOBJS) $(DCOBJS) $(CCCOBJS) $(RCOBJS)
