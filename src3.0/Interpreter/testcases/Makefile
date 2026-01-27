include ../../Makefile.config

GCC=clang
GCCOPT=-Wno-attributes -Wno-incompatible-pointer-types
DIS=$(LLVM)/bin/llvm-dis
LLI=$(LLVM)/bin/lli
MyLLI=./lynx

CFILES=$(wildcard *.c)
CPPFILES=$(wildcard *.cpp)
BCFILES=$(CFILES:.c=.bc)
BCFILES+=$(CPPFILES:.cpp=.bc)
LLFILES=$(CFILES:.c=.ll)
LLFILES+=$(CPPFILES:.cpp=.ll)

.PRECIOUS: $(BCFILES) $(LLFILES)

MYLLIOPT=
ifdef DEBUG
  MYLLIOPT+=-d  	
endif

all: $(BCFILES) $(LLFILES)
	+make -C llvm
	+make -C softbound
	sh spec.sh

%.bc: %.c
	$(GCC) $(GCCOPT) -emit-llvm -c $< -o $@

%.bc: %.cpp
	$(GCC) $(GCCOPT) -emit-llvm -c $< -o $@

%.ll: %.bc	
	$(DIS) $< -f -o $@
	$(LLI) $< 1 2 3 4 5 6 7 8 9
	$(MyLLI) $(MYLLIOPT) $< 1 2 3 4 5 6 7 8 9

clean:
	rm -f $(BCFILES) $(LLFILES)
	+make -C llvm clean
	+make -C softbound clean

