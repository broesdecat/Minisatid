MTL       = ../mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h) $(wildcard aggs/*.h) parse.tab.hh
CSRCS     = $(wildcard *.C) $(wildcard aggs/*.C)
EXEC      = minisatid
CFLAGS    = -I$(MTL) -I/export/home1/NoCsBack/dtai/broes/include -Iaggs -I../solveridsmt -Wall -ffloat-store
LFLAGS    = -lz

include ../mtl/template.mk
