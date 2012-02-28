include ../Makefile.config

COQARG=-I ./ott -I ./monads -I $(METALIB) -I ./compcert -I ./GraphBasics \
	-impredicative-set

all:
	+make -C $(METALIB)
	+make -C ./monads
	+make -C ./ott
	+make -C ./compcert 
	+make -C ./GraphBasics
	+make ott 
	+make -f Makefile.coq

ott: typings.vo

syntax.vo : ./monads/monad.vo ./compcert/Floats.vo ./compcert/alist.vo \
	./compcert/Memory.vo syntax.v
	$(COQC) $(COQARG) syntax.v

syntax.v : syntax.ott 
	$(OTT) -i syntax.ott -o syntax.v
	./fixott.py syntax.v

typings.v: syntax.ott infrastructure.vo typings.ott
	$(OTT) -merge false \
            -i syntax.ott -o _tmp_syntax.v \
	    -i typings.ott -o typings.v
	rm _tmp_syntax.v

targetdata.vo: targetdata.v syntax.vo
	$(COQC) $(COQARG) targetdata.v

analysis.vo: analysis.v infrastructure_props.vo GraphBasics/Dipaths.vo
	$(COQC) $(COQARG) analysis.v

infrastructure.vo: infrastructure.v syntax.vo targetdata.vo
	$(COQC) $(COQARG) infrastructure.v

infrastructure_props.vo: infrastructure_props.v infrastructure.vo
	$(COQC) $(COQARG) infrastructure_props.v

typings.vo: typings.v analysis.vo
	$(COQC) $(COQARG) typings.v

clean: 
	+make -C ./ott clean
	+make -C ./compcert clean
	+make -C ./monads clean	
	+make -C ./llvm_op clean
	+make -f Makefile.coq clean
	rm -rf main.pdf main.log main.aux main.log syntax.v \
		typings.vo *.vo *.glob merge.ott m_*.ott

