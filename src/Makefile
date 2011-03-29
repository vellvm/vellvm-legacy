include ./Makefile.config

OUTPUT_TYPE=native
OCAMLBUILD_OPT=-no-links -j 0 -cflags -g,-I,$(LLVM_OCAML_LIB) -lflags -g,-I,$(LLVM_OCAML_LIB),-cclib,-lffi,-cclib,-L$(LLVM_LIB)

all:
	+make -C ./ssa
	+make -C ./TV
	+make -C ./Extraction
	ocamlbuild -I Extraction $(OCAMLBUILD_OPT) Parser/main.$(OUTPUT_TYPE)
	ocamlbuild -Is Extraction,Parser $(OCAMLBUILD_OPT) Interpreter/main.$(OUTPUT_TYPE)
	ocamlbuild -Is Extraction,Parser $(OCAMLBUILD_OPT) TV/main.d.byte

clean:
	+make -C ./ssa clean
	+make -C ./TV clean
	+make -C ./Extraction clean
	ocamlbuild -clean

