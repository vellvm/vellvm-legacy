include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-links -j 0 -build-dir _build \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)
CMAS:=Extraction/_build/ssa_interpreter.cma \
  Extraction/_build/coq2llvm.cma \
  Extraction/_build/coq_pretty_printer.cma \
  Extraction/_build/eq_tv.cma \
  Extraction/_build/sub_tv.cma
CMXAS:=$(CMAS:.cma=.cmxa)

all: coq ocaml

coq:
	+make -C ./ssa
	+make -C ./TV
	+make -C ./Extraction

ocaml: coq $(CMAS) $(CMXAS)
	ocamlbuild -clean
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.d.byte
	ocamlbuild -Is Parser $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)

clean:
	+make -C ./ssa clean
	+make -C ./TV clean
	+make -C ./Extraction clean
	ocamlbuild -clean

ocamlclean:
	ocamlbuild -clean

.PHONY: all clean ocamlclean ocaml coq
