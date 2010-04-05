OTT=ott
COQC=coqc

all:
	+make -C ./monads
	+make -C ./ott
	+make ott

ott: ssa_def.v ssa_coq_lib.vo main.pdf ssa_lib.v Makefile ssa_static.vo

allott: ott ssa_all.v Makefile

ssa_coq_lib.vo : ssa_coq_lib.v ssa_def.vo Makefile
	$(COQC) -I ./ott ssa_coq_lib.v

ssa_def.vo : ssa_def.v Makefile
	$(COQC) -I ./ott ssa_def.v

ssa_def.v : ssa_def.ott Makefile
	ott -coq_expand_list_types false -i ssa_def.ott -o ssa_def.v

ssa_coq.ott : ssa_coq_lib.vo ssa_def.ott Makefile coq2ott.py Makefile
	./coq2ott.py
	cp merge.ott ssa_coq.ott       

m_ssa_static.ott : ssa_static.ott spanlines.py Makefile
	./spanlines.py ssa_static.ott

ssa_lib.v: ssa_def.ott ssa_coq.ott ssa_lib.ott Makefile ssa_def.v ssa_coq_lib.vo 
	ott -merge true -coq_expand_list_types false \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott -o ssa_lib.v
	$(COQC) -I ./ott ssa_lib.v

ssa_all.v: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott Makefile ssa_def.v ssa_coq_lib.vo 
	ott -merge true -coq_expand_list_types false \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott \
	    -i m_ssa_static.ott -i ssa_dynamic.ott -o ssa_all.v
	$(COQC) -I ./ott ssa_all.v

ssa_static.vo: ssa_static.v ssa_lib.v ./monads/Monad.vo
	$(COQC) -I ./ott -I ./monads ssa_static.v

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

