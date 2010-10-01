OTT=ott
COQC=coqc
COQARG=-I .. -I ../ott -I ../monads -I ~/SVN/provers/metalib/branches/metatheory_8.3/

all: main.pdf Makefile ssa_verifier.vo ssa_interpreter.vo ssa_all.vo

m_ssa_verifier.ott : ssa_verifier.ott ../spanlines.py Makefile
	../spanlines.py ssa_verifier.ott

ssa_lib.v: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott emacs.ott Makefile ../ssa_def.v ../ssa_coq_lib.vo ../monads/monad.vo
	ott -merge false -coq_expand_list_types true \
            -i ../ssa_def.ott -i ../ssa_coq.ott -i ../ssa_lib.ott \
	    -i emacs.ott -o ssa_lib.v

ssa_lib.vo: ssa_lib.v
	$(COQC) $(COQARG) ssa_lib.v

ssa_all.v: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott emacs.ott Makefile ../ssa_def.v ../ssa_coq_lib.vo ../monads/monad.vo
	ott -merge false -coq_expand_list_types true \
            -i ../ssa_def.ott -i ../ssa_coq.ott -i ../ssa_lib.ott \
	    -i m_ssa_verifier.ott -i ssa_interpreter.ott -i emacs.ott -o ssa_all.v

ssa_all.vo: ssa_all.v
	$(COQC) $(COQARG) ssa_all.v

ssa_verifier.vo: ssa_verifier.v ../ssa.vo ../monads/monad.vo ssa_lib.vo
	$(COQC) $(COQARG) ssa_verifier.v

ssa_interpreter.vo: ssa_interpreter.v ../ssa.vo ../monads/monad.vo ssa_lib.vo
	$(COQC) $(COQARG) ssa_interpreter.v

ssa.tex: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott omain.tex Makefile
	$(OTT) -merge false -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_all.v ssa_lib.v *.vo *.glob merge.ott m_*.ott

