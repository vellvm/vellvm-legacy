OTT=ott
COQC=coqc

all: main.pdf Makefile ssa_static.vo ssa_dynamic.vo ssa_all.v

m_ssa_static.ott : ssa_static.ott ../spanlines.py Makefile
	../spanlines.py ssa_static.ott

ssa_all.v: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott emacs.ott Makefile ../ssa_def.v ../ssa_coq_lib.vo ../monads/monad.vo
	ott -merge true -coq_expand_list_types false \
            -i ../ssa_def.ott -i ../ssa_coq.ott -i ../ssa_lib.ott \
	    -i m_ssa_static.ott -i ssa_dynamic.ott -i emacs.ott -o ssa_all.v
	$(COQC) -I ../ott -I ../monads ssa_all.v

vmcore.vo: vmcore.v ../ssa_lib.vo
	$(COQC) -I ../ott -I ../monads -I ../ vmcore.v

ssa_static.vo: ssa_static.v ../ssa_lib.vo ../monads/monad.vo ../reflect.vo vmcore.vo
	$(COQC) -I ../ott -I ../monads -I ../ ssa_static.v

ssa_dynamic.vo: ssa_dynamic.v ../ssa_lib.vo ../monads/monad.vo ../reflect.vo vmcore.vo
	$(COQC) -I ../ott -I ../monads -I ../ ssa_dynamic.v

ssa.tex: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott omain.tex Makefile
	$(OTT) -merge true -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_static.ott ssa_dynamic.ott

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_all.v *.vo *.glob merge.ott m_*.ott

