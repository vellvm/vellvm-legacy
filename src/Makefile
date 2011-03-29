include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-links -j 0 \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)

CMAS:=Extraction/ssa_lib.cma \
  Extraction/ssa_interpreter.cma \
  Extraction/eq_tv.cma \
  Extraction/sub_tv.cma \
  Extraction/coq2llvm.cma \
  Extraction/coq_pretty_printer.cma

CMXAS:=$(CMAS:.cma=.cmxa)

all: coq ocamllib ocamlexe


coq:
	+make -C ./ssa
	+make -C ./TV
	+make -C ./Extraction

ocamllib: coq
	ocamlbuild -I Extraction $(OCAMLBUILD_OPT) $(CMAS)
	ocamlbuild -I Extraction $(OCAMLBUILD_OPT) $(CMXAS)

ocamlexe: ocamllib
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.$(OUTPUT_TYPE)
	ocamlbuild -Is Parser $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)
	ocamlbuild -Is Parser $(OCAMLBUILD_OPT) TV/main.d.byte

clean:
	+make -C ./ssa clean
	+make -C ./TV clean
	+make -C ./Extraction clean
	ocamlbuild -clean

ocamlclean:
	ocamlbuild -clean

.PHONY: all coq ocamllib ocamlexe clean ocamlclean
