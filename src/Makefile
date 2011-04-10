include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-links -j 0 -build-dir _build \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)

CMAS:=Extraction/ssa_lib.cma \
  Extraction/ssa_interpreter.cma \
  Extraction/eq_tv.cma \
  Extraction/sub_tv.cma \
  Extraction/coq2llvm.cma \
  Extraction/coq_pretty_printer.cma

CMXAS:=$(CMAS:.cma=.cmxa)

all: 
	+make -C ./ssa
	+make -C ./TV
	+make -C ./Extraction
	ocamlbuild -clean
	ocamlbuild $(OCAMLBUILD_OPT) $(CMAS) $(CMXAS)
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.d.byte
	ocamlbuild -Is Parser $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)

clean:
	+make -C ./ssa clean
	+make -C ./TV clean
	+make -C ./Extraction clean
	ocamlbuild -clean

ocamlclean:
	ocamlbuild -clean

.PHONY: all clean ocamlclean
