OTT=ott
COQC=coqc

all: main.pdf ssa.v ssa_def.v ssa_lib.vo

ssa_lib.vo : ssa_lib.v
	$(COQC) -I ./ott ssa_lib.v

ssa_def.v : ssa_def.ott Makefile
	ott -coq_expand_list_types false -coq ssa_def.v \
            ssa_def.ott 
	$(COQC) -I ./ott ssa_def.v

ssa.v : ssa_def.ott ssa_coq.ott ssa_lib.ott ssa_static.ott ssa_dynamic.ott Makefile ssa_def.v ssa_lib.vo
	./coq2ott.py
	mv merge.ott ssa_coq.ott       
	ott -merge true -coq_expand_list_types false -coq ssa.v \
            ssa_def.ott ssa_coq.ott ssa_lib.ott ssa_static.ott ssa_dynamic.ott
	$(COQC) -I ./ott ssa.v

ssa.tex: ssa_def.ott ssa_coq.ott ssa_lib.ott ssa_static.ott ssa_dynamic.ott omain.tex Makefile
	$(OTT) -merge true -tex ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ssa_def.ott ssa_coq.ott ssa_lib.ott ssa_static.ott ssa_dynamic.ott
          

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa.v ssa_def.v *.vo *.glob merge.ott

