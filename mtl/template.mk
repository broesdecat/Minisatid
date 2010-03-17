##
##  Template makefile for Standard, Profile, Debug, Release, and Release-static versions
##
##    eg: "make rs" for a statically linked release version.
##        "make d"  for a debug version (no optimizations).
##        "make"    for the standard version (optimized, but with debug information and assertions active)
##		added: Code coverage version (CC prefix): no optimization, extra options, to use gcov

CSRCS     ?= $(wildcard *.C)
CHDRS     ?= $(wildcard *.h)
COBJS     ?= $(addsuffix .o, $(basename $(CSRCS))) #parse.tab.o lex.yy.o

PCOBJS     = $(addsuffix p,  $(COBJS)) #parse.tab.o lex.yy.o
DCOBJS     = $(addsuffix d,  $(COBJS)) #parse.tab.o lex.yy.o
RCOBJS     = $(addsuffix r,  $(COBJS)) #parse.tab.o lex.yy.o
CCCOBJS     = $(addsuffix cc,  $(COBJS)) #parse.tab.o lex.yy.o

EXEC      ?= $(notdir $(shell pwd))
LIB       ?= $(EXEC)

CXX       ?= g++
CFLAGS    ?= -Wall
LFLAGS    ?= -Wall

COPTIMIZE ?= -O3

.PHONY : s cc p d r rs lib libd clean 

s:	$(EXEC)
p:	$(EXEC)_profile
d:	$(EXEC)_debug
r:	$(EXEC)_release
cc: $(EXEC)_codecover
rs:	$(EXEC)_static
lib:	lib$(LIB).a
libd:	lib$(LIB)d.a

## Compile options
%.o:			CFLAGS +=$(COPTIMIZE) -ggdb -D DEBUG
%.occ:		CFLAGS +=-O0 -fprofile-arcs -ftest-coverage -ggdb -D DEBUG # -D INVARIANTS
%.op:			CFLAGS +=$(COPTIMIZE) -pg -ggdb -D NDEBUG
%.od:			CFLAGS +=-O0 -ggdb -D DEBUG # -D INVARIANTS
%.or:			CFLAGS +=$(COPTIMIZE) -D NDEBUG

## Link options
$(EXEC):					LFLAGS := -ggdb $(LFLAGS)
$(EXEC)_codecover: 	LFLAGS := -ggdb -lgcov $(LFLAGS)
$(EXEC)_profile:		LFLAGS := -ggdb -pg $(LFLAGS)
$(EXEC)_debug:			LFLAGS := -ggdb $(LFLAGS)
$(EXEC)_release:		LFLAGS := $(LFLAGS)
$(EXEC)_static:		LFLAGS := --static $(LFLAGS)

## Dependencies
$(EXEC):					$(COBJS)
$(EXEC)_codecover:	$(CCCOBJS)
$(EXEC)_profile:		$(PCOBJS)
$(EXEC)_debug:			$(DCOBJS)
$(EXEC)_release:		$(RCOBJS)
$(EXEC)_static:		$(RCOBJS)

lib$(LIB).a:	$(filter-out Main.or, $(RCOBJS))
lib$(LIB)d.a:	$(filter-out Main.od, $(DCOBJS))


## Build rule
%.o %.op %.od %.or %.occ:	%.C
	@echo Compiling: "$@ ( $< )"
	@$(CXX) $(CFLAGS) -c -o $@ $<
	
#%.o:	%.c
#	@$(CXX) $(CFLAGS) -c -o $@ $<

#%.tab.C:%.yy
#	bison --defines --output=$@ $<

#%.yy.c:	%.ll
#	flex -o$@ $<


## Linking rules (standard/profile/debug/release)
$(EXEC) $(EXEC)_codecover $(EXEC)_profile $(EXEC)_debug $(EXEC)_release $(EXEC)_static:
	@echo Linking: "$@ ( $^ )"
	@$(CXX) $^ $(LFLAGS) -o $@

## Library rule
lib$(LIB).a lib$(LIB)d.a:
	@echo Library: "$@ ( $^ )"
	@rm -f $@
	@ar cq $@ $^

## Clean rule
clean:
	@rm -f $(EXEC) $(EXEC)_codecover $(EXEC)_profile $(EXEC)_debug $(EXEC)_release $(EXEC)_static \
	  $(COBJS) $(CCCOBJS) $(PCOBJS) $(DCOBJS) $(RCOBJS) *.core depend.mak lib$(LIB).a lib$(LIB)d.a

## Make dependencies
depend.mk: $(CSRCS) $(CHDRS)
	@echo Making dependencies ...
	@echo $(CSRCS)
	@$(CXX) $(CFLAGS) -MM $(CSRCS) > depend.mk
	@cp depend.mk /tmp/depend.mk.tmp
	@sed "s/o:/occ:/" /tmp/depend.mk.tmp >> depend.mk
	@sed "s/o:/op:/" /tmp/depend.mk.tmp >> depend.mk
	@sed "s/o:/od:/" /tmp/depend.mk.tmp >> depend.mk
	@sed "s/o:/or:/" /tmp/depend.mk.tmp >> depend.mk
	@rm /tmp/depend.mk.tmp

-include depend.mk
