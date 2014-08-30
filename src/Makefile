include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-hygiene -no-links -j 0 -build-dir _build \
  -cflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB) \
  -lflags -g,-I,$(LLVM_OCAML_LIB),-I,$(EXTRACTION_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)

COQLIBS=-I Vellvm/ -I Vellvm/ott -I Vellvm/compcert -I Vellvm/Dominators \
	-I $(LIB)/GraphBasics -I $(LIB)/compcert \
	-I $(METALIB) -R $(EQUATIONS)/theories Equations -I $(EQUATIONS)/src
MAKECOQ=make -f Makefile.coq COQLIBS="$(COQLIBS)"

all: theories

theories: Makefile.coq Vellvm/syntax_base.v Vellvm/typing_rules.v
	+$(MAKECOQ)

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

%.vo: Makefile.coq Vellvm/syntax_base.v Vellvm/typing_rules.v
	+$(MAKECOQ) "$@"

ocaml: theories
	+make -f Makefile.ocaml -C Extraction
	ocamlbuild -clean
	ocamlbuild $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)
	ocamlbuild $(OCAMLBUILD_OPT) Vellvm/Dominators/main.native
	ocamlbuild $(OCAMLBUILD_OPT) Parser/main.d.byte

dtree: theories
	ocamlbuild Vellvm/Dominators/main.native -clean
	ocamlbuild $(OCAMLBUILD_OPT) Vellvm/Dominators/main.native

clean:
	rm -rf Vellvm/main.pdf Vellvm/main.log Vellvm/main.aux \
		Vellvm/syntax_base.v Vellvm/typing_rules.v Vellvm/m_*.ott
	+make -f Makefile.coq clean
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

.PHONY: all clean ocamlclean ocaml theories extraction
