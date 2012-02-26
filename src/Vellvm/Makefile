include ../Makefile.config

all: coq

coq: Makefile.coq syntax.v typings.v
	+make -f Makefile.coq

Makefile.coq: Make
	coq_makefile -f Make -I $(METALIB) -o Makefile.coq -no-install

ott: main.pdf typings.vo interpreter.vo opsem_inst.vo vellvm.vo opsem_dom.vo

syntax.v : syntax.ott
	$(OTT) -coq_expand_list_types true -i syntax.ott -o syntax.v
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
	+make -C ./ott clean
	+make -C ./compcert clean
	+make -C ./monads clean
	rm -rf main.pdf main.log main.aux syntax.v typings.v m_*.ott
	if [ -f Makefile.coq ]; then        \
		make -f Makefile.coq clean; \
		rm Makefile.coq;            \
	fi

.PHONY: all coq clean ott
