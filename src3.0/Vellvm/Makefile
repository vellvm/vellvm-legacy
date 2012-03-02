include ../Makefile.config

all: syntax.v typings.v

syntax.v : syntax.ott
	$(OTT) -i syntax.ott -o syntax.v
	./fixott.py syntax.v

m_typings.ott : typings.ott spanlines.py
	./spanlines.py typings.ott

typings.v: syntax.ott m_typings.ott
	$(OTT) -merge false -coq_expand_list_types true \
            -i syntax.ott -o _tmp_syntax.v \
	    -i m_typings.ott -o typings.v
	rm _tmp_syntax.v
	./fixott.py typings.v

def.tex: syntax.ott m_typings.ott main.tex
	$(OTT) -merge false -o def.tex \
          -tex_show_meta false \
          -tex_wrap false \
            syntax.ott m_typings.ott

main.pdf: def.tex main.tex macros.sty
	pdflatex main.tex
	pdflatex main.tex

clean:
	rm -rf main.pdf main.log main.aux syntax.v typings.v m_*.ott

.PHONY: all clean
