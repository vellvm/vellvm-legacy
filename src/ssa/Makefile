OTT=ott
COQC=coqc

all:
	+make -C ./monads
	+make -C ./ott
	+make ott

ott: ssa_def.v ssa_coq_lib.vo main.pdf ssa_lib.v Makefile ssa_static.vo ssa_dynamic.vo

allott: ott ssa_all.v Makefile

ssa_coq_lib.vo : ssa_coq_lib.v ssa_def.vo Makefile
	$(COQC) -I ./ott -I ./monads ssa_coq_lib.v

ssa_def.vo : ssa_def.v Makefile ./monads/monad.vo
	$(COQC) -I ./ott -I ./monads ssa_def.v

ssa_def.v : ssa_def.ott emacs.ott Makefile
	ott -coq_expand_list_types false -i ssa_def.ott -i emacs.ott -o ssa_def.v

ssa_coq.ott : ssa_coq_lib.vo ssa_def.ott Makefile coq2ott.py Makefile
	./coq2ott.py
	cp merge.ott ssa_coq.ott       

m_ssa_static.ott : ssa_static.ott spanlines.py Makefile
	./spanlines.py ssa_static.ott

ssa_lib.v: ssa_def.ott ssa_coq.ott ssa_lib.ott emacs.ott Makefile ssa_def.v ssa_coq_lib.vo ./monads/monad.vo
	ott -merge true -coq_expand_list_types false \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott -i emacs.ott -o ssa_lib.v

ssa_lib.vo: ssa_lib.v
	$(COQC) -I ./ott -I ./monads ssa_lib.v

ssa_all.v: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott emacs.ott Makefile ssa_def.v ssa_coq_lib.vo ./monads/monad.vo
	ott -merge true -coq_expand_list_types false \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott \
	    -i m_ssa_static.ott -i ssa_dynamic.ott -i emacs.ott -o ssa_all.v
	$(COQC) -I ./ott -I ./monads ssa_all.v

reflect.vo: reflect.v ssa_lib.vo
	$(COQC) -I ./ott -I ./monads reflect.v

vmcore.vo: vmcore.v ssa_lib.vo
	$(COQC) -I ./ott -I ./monads vmcore.v

ssa_static.vo: ssa_static.v ssa_lib.vo ./monads/monad.vo reflect.vo vmcore.vo
	$(COQC) -I ./ott -I ./monads ssa_static.v

ssa_dynamic.vo: ssa_dynamic.v ssa_lib.vo ./monads/monad.vo reflect.vo vmcore.vo
	$(COQC) -I ./ott -I ./monads ssa_dynamic.v

ssa.tex: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott omain.tex Makefile
	$(OTT) -merge true -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_def.v ssa_lib.v ssa_all.v *.vo *.glob merge.ott m_*.ott

