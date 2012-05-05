include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-hygiene -no-links -j 0 -build-dir _build \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)
#CMAS:=Extraction/_build/coqllvm.cma \
#  Extraction/_build/eq_tv.cma \
#  Extraction/_build/sub_tv.cma
#CMXAS:=$(CMAS:.cma=.cmxa)
COQLIBS=-I Vellvm/ -I Vellvm/ott -I Vellvm/monads -I Vellvm/compcert \
	-I Vellvm/GraphBasics -I Transforms -I TV -I SoftBound \
	-I $(METALIB)
MAKECOQ=make -f Makefile.coq COQLIBS="$(COQLIBS)"

all: theories extraction ocaml

theories: Makefile.coq Vellvm/syntax_base.v Vellvm/typing_rules.v
	+$(MAKECOQ)

extraction: theories
	+make -C Extraction
	+cd Extraction; ./fixextract.py; cd ..

# For some reason, the -slash option of coqdep is generating
# ill-formed .v.d files. Removing it seems to fix the problem.
Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq
	sed -e 's/-slash //' -i Makefile.coq

%.vo: Makefile.coq Vellvm/syntax_base.v Vellvm/typing_rules.v
	+$(MAKECOQ) "$@"

ocaml: theories extraction
	+make -f Makefile.ocaml -C Extraction
	ocamlbuild -clean
	ocamlbuild $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)
	ocamlbuild $(OCAMLBUILD_OPT) Transforms/main.native
	ocamlbuild $(OCAMLBUILD_OPT) SoftBound/main.d.byte
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.d.byte

dtree: theories extraction
	+make -f Makefile.ocaml -C Extraction
	ocamlbuild Vellvm/Dominators/main.native -clean
	ocamlbuild $(OCAMLBUILD_OPT) Vellvm/Dominators/main.native

mem2reg: theories extraction
	+make -f Makefile.ocaml -C Extraction
	ocamlbuild Transforms/main.native -clean
	ocamlbuild $(OCAMLBUILD_OPT) Transforms/main.native

clean:
	rm -rf Vellvm/main.pdf Vellvm/main.log Vellvm/main.aux \
		Vellvm/syntax_base.v Vellvm/typing_rules.v Vellvm/m_*.ott
	+make -f Makefile.coq clean
	+make -C ./Extraction clean
	+make -f Makefile.ocaml -C Extraction clean
	ocamlbuild -clean

ocamlclean:
	+make -C ./Extraction -f Makefile.ocaml clean
	ocamlbuild -clean

Vellvm/syntax_base.v : Vellvm/syntax_base.ott
	cd Vellvm && \
	$(OTT) -coq_expand_list_types false -i syntax_base.ott -o syntax_base.v

Vellvm/typing_rules.v: Vellvm/syntax_base.ott Vellvm/typing_rules.ott
	cd Vellvm && \
	$(OTT) -merge false -coq_expand_list_types false \
            -i syntax_base.ott -o _tmp_syntax_base.v \
	    -i typing_rules.ott -o typing_rules.v && \
	rm _tmp_syntax_base.v

Vellvm/def.tex: Vellvm/syntax_base.ott Vellvm/m_typings.ott Vellvm/main.tex
	cd Vellvm && \
	$(OTT) -merge false -o def.tex \
          -tex_show_meta false \
          -tex_wrap false \
            syntax_base.ott m_typings.ott

Vellvm/main.pdf: Vellvm/def.tex Vellvm/main.tex Vellvm/macros.sty
	cd Vellvm && \
	pdflatex main.tex && \
	pdflatex main.tex

.PHONY: all clean ocamlclean ocaml theories extraction
