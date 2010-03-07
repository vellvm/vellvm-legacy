OTT=ott

all: main.pdf ssa.v

ssa.v : ssa.ott 
	ott  -coq_expand_list_types true -coq ssa.v \
            ssa.ott

ssa.tex: ssa.ott omain.tex Makefile
	$(OTT) -tex ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
          ssa.ott

main.pdf: ssa.tex main.tex macros.sty Makefile
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa.v ssa.vo ssa.glob

