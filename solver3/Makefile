MTL       = ../mtl
PHDRS		 = ../solvers/ecnf.y.hpp
CHDRS     = $(wildcard *.hpp) $(wildcard $(MTL)/*.hpp) $(wildcard ../solvers/*.hpp) $(wildcard ../solvers/aggs/*.hpp) #$(wildcard ../bigint/*.hh) #parse.tab.hh
PSRCS		 = ../solvers/ecnf.y.cpp ../solvers/ecnf.l.cpp
CSRCS     = $(wildcard *.cpp) $(wildcard ../solvers/*.cpp) $(wildcard ../solvers/aggs/*.cpp) $(PSRCS) #$(wildcard ../bigint/*.C)
EXEC      = minisat3
CFLAGS    = -I$(MTL) -I../solvers -I../solvers/aggs -I. -I../bigint -Wall -Wextra -Wno-unused-parameter -ffloat-store -pedantic -Wno-variadic-macros #-D GMP -fno-strict-aliasing
LFLAGS    = #-lz -lgmpxx -lgmp

include ../mtl/template2.mk
