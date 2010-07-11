OTT=ott
COQC=coqc

all: main.pdf Makefile ssa_verifier.vo ssa_interpreter.vo ssa_all.v

m_ssa_verifier.ott : ssa_verifier.ott ../spanlines.py Makefile
	../spanlines.py ssa_verifier.ott

ssa_lib.v: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott emacs.ott Makefile ../ssa_def.v ../ssa_coq_lib.vo ../monads/monad.vo
	ott -merge true -coq_expand_list_types false \
            -i ../ssa_def.ott -i ../ssa_coq.ott -i ../ssa_lib.ott \
	    -i emacs.ott -o ssa_lib.v

ssa_lib.vo: ssa_lib.v
	$(COQC) -I ../ott -I ../monads ssa_lib.v

ssa_all.v: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott emacs.ott Makefile ../ssa_def.v ../ssa_coq_lib.vo ../monads/monad.vo
	ott -merge true -coq_expand_list_types false \
            -i ../ssa_def.ott -i ../ssa_coq.ott -i ../ssa_lib.ott \
	    -i m_ssa_verifier.ott -i ssa_interpreter.ott -i emacs.ott -o ssa_all.v
	$(COQC) -I ../ott -I ../monads ssa_all.v

ssa_verifier.vo: ssa_verifier.v ../ssa.vo ../monads/monad.vo ssa_lib.vo
	$(COQC) -I ../ott -I ../monads ssa_verifier.v

ssa_interpreter.vo: ssa_interpreter.v ../ssa.vo ../monads/monad.vo ssa_lib.vo
	$(COQC) -I ../ott -I ../monads ssa_interpreter.v

ssa.tex: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott omain.tex Makefile
	$(OTT) -merge true -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_all.v ssa_lib.v *.vo *.glob merge.ott m_*.ott

