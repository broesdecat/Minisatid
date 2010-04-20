MTL       = ../mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h) $(wildcard ../solvers/*.h) $(wildcard ../solvers/aggs/*.h) $(wildcard ../bigint/*.hh) #parse.tab.hh
CSRCS     = $(wildcard *.C) $(wildcard ../solvers/*.C) $(wildcard ../solvers/aggs/*.C) $(wildcard ../bigint/*.C)
EXEC      = minisat3
CFLAGS    = -I$(MTL) -I../solvers -I../solvers/aggs -I. -I../bigint -Wall -ffloat-store -pedantic -Wno-variadic-macros #-D GMP -fno-strict-aliasing
LFLAGS    = -lz -lgmpxx -lgmp

include ../mtl/template2.mk
