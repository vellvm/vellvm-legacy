OTT=ott
COQC=coqc

all:
	+make -C ./monads
	+make -C ./ott
	+make ott 
	+make -C ./llvm_op

ott: ssa_def.v ssa_coq_lib.vo main.pdf ssa.vo Makefile

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

ssa.v: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott emacs.ott Makefile ssa_def.v ssa_coq_lib.vo ./monads/monad.vo
	ott -merge true -coq_expand_list_types false \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott -i m_ssa_static.ott -i emacs.ott -o ssa.v

ssa.vo: ssa.v
	$(COQC) -I ./ott -I ./monads ssa.v

ssa.tex: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott omain.tex Makefile
	$(OTT) -merge true -o ssa.tex \
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

