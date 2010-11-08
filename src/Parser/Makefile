
include ../Makefile.config

OUTPUT_TYPE := byte

all: main

main: main.ml $(TV_LIB)/symexe_correct.cma $(LLVM_OCAML_LIB)/llvm.cma
	ocamlbuild -j 2 -cflags -I,$(LLVM_OCAML_LIB),-I,$(TV_LIB) -lflags -I,$(LLVM_OCAML_LIB),-I,$(TV_LIB),-cclib,-L$(LLVM_LIB) main.$(OUTPUT_TYPE)
	mv main.$(OUTPUT_TYPE) main

.PHONY: wc
wc:
	wc main.ml

.PHONY: clean
clean:
	ocamlbuild -clean
	rm -rf a.out

