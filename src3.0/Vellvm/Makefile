include ../Makefile.config

COQARG=-I ./ott -I ./monads -I $(METALIB) -I ./compcert -I ./GraphBasics \
	-impredicative-set

all:
	+make -C $(METALIB)
	+make -C ./monads
	+make -C ./ott
	+make -C ./compcert 
	+make -C ./GraphBasics
	+make ott 

ott: typings.vo interpreter.vo opsem_inst.vo vellvm.vo opsem_dom.vo

syntax.vo : ./monads/monad.vo ./compcert/Floats.vo ./compcert/alist.vo \
	./compcert/Memory.vo syntax.v
	$(COQC) $(COQARG) syntax.v

syntax.v : syntax.ott 
	$(OTT) -i syntax.ott -o syntax.v
	./fixott.py syntax.v

typings.v: syntax.ott infrastructure.vo \
	typings.ott ./monads/monad.vo targetdata.vo
	$(OTT) -merge false \
            -i syntax.ott -o _tmp_syntax.v \
	    -i typings.ott -o typings.v
	rm _tmp_syntax.v

infrastructure.vo: infrastructure.v syntax.vo targetdata.vo
	$(COQC) $(COQARG) infrastructure.v

typings.vo: typings.v infrastructure.vo analysis.vo
	$(COQC) $(COQARG) typings.v

targetdata.vo: targetdata.v syntax.vo
	$(COQC) $(COQARG) targetdata.v

analysis.vo: compcert/Kildall.vo analysis.v infrastructure.vo \
	infrastructure_props.vo compcert/Memory.vo GraphBasics/Dipaths.vo
	$(COQC) $(COQARG) analysis.v

genericvalues.vo: syntax.vo infrastructure.vo compcert/tactics.vo \
	compcert/trace.vo genericvalues.v targetdata.vo compcert/Memory.vo
	$(COQC) $(COQARG) genericvalues.v

interpreter.vo: interpreter.v syntax.vo infrastructure.vo genericvalues.vo \
	infrastructure_props.vo dopsem.vo
	$(COQC) $(COQARG) interpreter.v

infrastructure_props.vo: infrastructure_props.v syntax.vo infrastructure.vo \
	compcert/Kildall.vo
	$(COQC) $(COQARG) infrastructure_props.v

typings_props.vo: typings_props.v syntax.vo infrastructure.vo genericvalues.vo \
	infrastructure_props.vo analysis.vo typings.vo
	$(COQC) $(COQARG) typings_props.v

targetdata_props.vo: targetdata_props.v syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo analysis.vo typings.vo
	$(COQC) $(COQARG) targetdata_props.v

genericvalues_props.vo: genericvalues_props.v syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo analysis.vo typings.vo \
	targetdata_props.vo typings_props.vo
	$(COQC) $(COQARG) genericvalues_props.v

static.vo: static.v typings_props.vo targetdata_props.vo genericvalues_props.vo
	$(COQC) $(COQARG) static.v

external_intrinsics.vo: external_intrinsics.v typings.vo
	$(COQC) $(COQARG) external_intrinsics.v

opsem.vo: opsem.v external_intrinsics.vo static.vo
	$(COQC) $(COQARG) opsem.v

opsem_props.vo: opsem_props.v opsem.vo syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem_props.v

opsem_wf.vo: opsem_wf.v opsem_props.vo opsem.vo syntax.vo infrastructure.vo\
       genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem_wf.v

opsem_dom.vo: opsem_dom.v opsem_wf.vo
	$(COQC) $(COQARG) opsem_dom.v

dopsem.vo: dopsem.v opsem_wf.vo
	$(COQC) $(COQARG) dopsem.v

ndopsem.vo: ndopsem.v opsem_wf.vo
	$(COQC) $(COQARG) ndopsem.v

opsem_inst.vo: opsem_inst.v ndopsem.vo dopsem.vo syntax.vo infrastructure.vo
	$(COQC) $(COQARG) opsem_inst.v

def.tex: syntax.ott typings.ott main.tex 
	$(OTT) -merge false -o def.tex \
          -tex_show_meta false \
          -tex_wrap false \
            syntax.ott typings.ott

vellvm.vo : vellvm.v dopsem.vo ndopsem.vo
	$(COQC) $(COQARG) vellvm.v

main.pdf: def.tex main.tex macros.sty 
	pdflatex main.tex
	pdflatex main.tex

clean: 
	+make -C ./ott clean
	+make -C ./compcert clean
	+make -C ./monads clean	
	+make -C ./llvm_op clean
	rm -rf main.pdf main.log main.aux main.log syntax.v \
		typings.vo *.vo *.glob merge.ott m_*.ott

