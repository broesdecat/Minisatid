MTL       = ../mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
EXEC      = minisat
CFLAGS    = -I$(MTL) -Wall -ffloat-store -O3 -fno-strict-aliasing -DNDEBUG -static #-m64
LFLAGS    = -lz

include ../mtl/template.mk
