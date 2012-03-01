include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-hygiene -no-links -j 0 -build-dir _build \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)
CMAS:=Extraction/_build/coqllvm.cma \
  Extraction/_build/eq_tv.cma \
  Extraction/_build/sub_tv.cma
CMXAS:=$(CMAS:.cma=.cmxa)

all: coq ocaml

coq:
	+make -C ./Vellvm
	+make -C ./SoftBound
	+make -C ./TV
	+make -C ./Transforms
	+make -C ./Extraction

ocaml: coq $(CMAS) $(CMXAS)
	ocamlbuild -clean
	ocamlbuild $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)
	ocamlbuild $(OCAMLBUILD_OPT) Transforms/main.native
	ocamlbuild $(OCAMLBUILD_OPT) SoftBound/main.d.byte
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.d.byte

clean:
	+make -C ./Vellvm clean
	+make -C ./SoftBound clean
	+make -C ./TV clean
	+make -C ./Transforms clean
	+make -C ./Extraction clean
	ocamlbuild -clean

ocamlclean:
	+make -C ./Extraction -f Makefile.ocaml clean
	ocamlbuild -clean

.PHONY: all clean ocamlclean ocaml coq
