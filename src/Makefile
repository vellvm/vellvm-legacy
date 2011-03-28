
all:
	+make -C ./ssa
	+make -C ./TV
	+make -C ./Parser
	+make -C ./Interpreter -f Makefile.ocaml

clean:
	+make -C ./ssa clean
	+make -C ./TV clean
	+make -C ./Parser clean
	+make -C ./Interpreter -f Makefile.ocaml clean

