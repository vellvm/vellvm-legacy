OTT=ott
COQC=coqc
COQARG=-I ./ott -I ./monads -I ../../../theory/metatheory/

all:
	+make -C ./monads
	+make -C ./ott
	+make ott 
	+make -C ./llvm_op

ott: main.pdf ssa.vo Makefile ssa_dynamic.vo opsem_conv.vo

ssa_coq_lib.vo : ssa_coq_lib.v ssa_def.vo Makefile
	$(COQC) $(COQARG) ssa_coq_lib.v

ssa_def.vo : ssa_def.v Makefile ./monads/monad.vo
	$(COQC) $(COQARG) ssa_def.v

ssa_def.v : ssa_def.ott emacs.ott Makefile
	ott -coq_expand_list_types false -i ssa_def.ott -i emacs.ott -o ssa_def.v

ssa_coq.ott : ssa_coq_lib.vo ssa_def.ott Makefile coq2ott.py Makefile
	./coq2ott.py
	cp merge.ott ssa_coq.ott       

m_ssa_static.ott : ssa_static.ott spanlines.py Makefile
	./spanlines.py ssa_static.ott

ssa.v: ssa_def.ott ssa_coq_lib.vo ssa_coq.ott ssa_lib.ott m_ssa_static.ott emacs.ott Makefile ./monads/monad.vo
	ott -merge false -coq_expand_list_types false \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott -i m_ssa_static.ott -i emacs.ott -o ssa.v

ssa.vo: ssa.v
	$(COQC) $(COQARG) ssa.v

tactics.vo: tactics.v
	$(COQC) tactics.v

targetdata.vo: targetdata.v ssa.vo
	$(COQC) $(COQARG) targetdata.v

ssa_mem.vo: ssa_mem.v ssa.vo tactics.vo targetdata.vo
	$(COQC) $(COQARG) ssa_mem.v

trace.vo: trace.v
	$(COQC) trace.v

ssa_dynamic.vo: ssa_dynamic.v ssa.vo tactics.vo ssa_mem.vo trace.vo
	$(COQC) $(COQARG) ssa_dynamic.v

opsem_conv.vo: opsem_conv.v ssa_dynamic.vo ssa.vo trace.vo
	$(COQC) $(COQARG) opsem_conv.v

ssa.tex: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott omain.tex Makefile
	$(OTT) -merge false -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	+make -C ./ott clean
	+make -C ./monads clean	
	+make -C ./llvm_op clean
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_def.v ssa.v *.vo *.glob merge.ott m_*.ott

