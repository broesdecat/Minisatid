MTL       = ../mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h) $(wildcard aggs/*.h) $(wildcard bigint/*.hh) parse.tab.hh
CSRCS     = $(wildcard *.C) $(wildcard aggs/*.C)  $(wildcard bigint/*.C)
EXEC      = minisat
CFLAGS    = -I$(MTL) -Iaggs -Ibigint -I../solveridsmtoutofdate -Wall -ffloat-store -pedantic -Wno-variadic-macros #-fno-strict-aliasing
LFLAGS    = -lz -lgmpxx -lgmp

include ../mtl/template2.mk
