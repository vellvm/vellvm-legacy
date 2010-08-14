OUTPUT_TYPE := byte
LLVM_LIB := /home/jianzhou/Tools/llvm-2.6/lib/
LLVM_OCAML_LIB := $(LLVM_LIB)/ocaml/

all: main

main: main.ml
	ocamlbuild -j 2 -cflags -I,$(LLVM_OCAML_LIB) -lflags -I,$(LLVM_OCAML_LIB),-cclib,-L$(LLVM_LIB) main.$(OUTPUT_TYPE)
	mv main.$(OUTPUT_TYPE) main

.PHONY: wc
wc:
	wc main.ml

.PHONY: clean
clean:
	ocamlbuild -clean
	rm -rf a.out

