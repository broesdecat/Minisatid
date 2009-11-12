### compilers and compile flags to use ###
GPP=g++
FLEX=flex
YACC=bison
# by default, include gdb debugging info, but exclude the external debugging stuff such as trail.
GPPFLAGS=-O3 -D NDEBUG
FLEXFLAGS=
YACCFLAGS=--defines
#GPPFLAGS=-ggdb
#FLEXFLAGS=
#YACCFLAGS=--verbose --debug --defines

# files to use
LEX=lex
GRAMMAR=parse
MAIN=main
OBJECTS=$(MAIN).o $(SOURCES) $(GRAMMAR).tab.o $(LEX).yy.o
OUTPUT=translation_tool

### make rules ###

all: translation_tool

translation_tool: $(OBJECTS)
	$(GPP) $(GPPFLAGS) -o $(OUTPUT) $(OBJECTS)

clean:
	-rm -f $(LEX).yy.c $(GRAMMAR).tab.cc $(GRAMMAR).output $(GRAMMAR).tab.hh $(OBJECTS)

# separate rule for this, because of ".yy.c" instead of ".yy.cc"
%.o:	%.c
	$(GPP) $(GPPFLAGS) -c -o $@ $<

%.o:	%.cc
	$(GPP) $(GPPFLAGS) -c -o $@ $<

%.tab.cc:%.yy
	$(YACC) $(YACCFLAGS) --output=$@ $<

%.yy.c:	%.ll
	$(FLEX) $(FLEXFLAGS) -o $@ $<
