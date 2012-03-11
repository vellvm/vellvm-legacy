include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-hygiene -no-links -j 0 -build-dir _build \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)
CMAS:=Extraction/_build/coqllvm.cma \
  Extraction/_build/eq_tv.cma \
  Extraction/_build/sub_tv.cma
CMXAS:=$(CMAS:.cma=.cmxa)
COQLIBS=-I Vellvm/ -I Vellvm/ott -I Vellvm/monads -I Vellvm/compcert \
	-I Vellvm/GraphBasics -I Transforms -I TV -I SoftBound \
	-I $(METALIB)

all: theories extraction ocaml

theories: Makefile.coq
	+make -C ./Vellvm
	+make -f Makefile.coq COQLIBS="$(COQLIBS)"

extraction: theories
	+make -C Extraction        
	+cd Extraction; ./fixextract.py; cd ..

# For some reason, the -slash option of coqdep is generating
# ill-formed .v.d files. Removing it seems to fix the problem.
Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq
	sed -e 's/-slash //' -i Makefile.coq

%.vo: Makefile.coq
	make -f Makefile.coq "$@"

ocaml: theories $(CMAS) $(CMXAS)
	+make -f Makefile.ocaml -C Extraction
	ocamlbuild -clean
	ocamlbuild $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)
	ocamlbuild $(OCAMLBUILD_OPT) Transforms/main.native
	ocamlbuild $(OCAMLBUILD_OPT) SoftBound/main.d.byte
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.d.byte

clean:
	+make -C ./Vellvm clean
	+make -f Makefile.coq clean
	+make -C ./Extraction clean
	+make -f Makefile.ocaml -C Extraction clean
	ocamlbuild -clean

ocamlclean:
	+make -C ./Extraction -f Makefile.ocaml clean
	ocamlbuild -clean

.PHONY: all clean ocamlclean ocaml theories extraction
