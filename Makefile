include ./Makefile.config

COQLIBS=-I src/Vellvm -I src/Vellvm/ott -I src/Vellvm/Dominators \
	-I lib/GraphBasics -I lib/compcert-1.9 -I lib/cpdtlib -I lib/metalib-20090714 \
	-R lib/Coq-Equations-8.4/theories Equations -I lib/Coq-Equations-8.4/src
MAKECOQ=make -f Makefile.coq COQLIBS="$(COQLIBS)"

all: theories

depend: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	+$(MAKECOQ) depend

theories: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	+$(MAKECOQ)

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

%.vo: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	+$(MAKECOQ) "$@"

clean:
	rm -f src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v 
	make -f Makefile.coq clean

src/Vellvm/syntax_base.v: src/Vellvm/syntax_base.ott
	cd src/Vellvm && \
	$(OTT) -coq_expand_list_types false -i syntax_base.ott -o syntax_base.v

src/Vellvm/typing_rules.v: src/Vellvm/syntax_base.ott src/Vellvm/typing_rules.ott
	cd src/Vellvm && \
	$(OTT) -merge false -coq_expand_list_types false \
            -i syntax_base.ott -o _tmp_syntax_base.v \
	    -i typing_rules.ott -o typing_rules.v && \
	rm _tmp_syntax_base.v

.PHONY: all clean theories
