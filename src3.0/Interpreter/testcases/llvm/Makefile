include ../../../Makefile.config

GCC=llvm-gcc
DIS=$(LLVM)/bin/llvm-dis
AS=$(LLVM)bin/llvm-as
LLI=$(LLVM)/bin/lli
MyLLI=../lynx

LLFILES=$(wildcard *.ll)
BCFILES=$(LLFILES:.ll=.bc)

MYLLIOPT=
ifdef DEBUG
  MYLLIOPT+=-d
endif

.PRECIOUS: $(BCFILES)

all: $(BCFILES) 

%.bc: %.ll
	$(AS) -f $< -o $@
	-$(LLI) $@
	-$(MyLLI) $(MYLLIOPT) $@

clean:
	rm -f $(BCFILES)
