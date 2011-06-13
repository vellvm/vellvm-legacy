include ../Makefile.config

COQARG=-I ./ott -I ./monads -I $(METALIB) -I ./compcert

all:
	+make -C $(METALIB)
	+make -C ./monads
	+make -C ./ott
	+make -C ./compcert 
	+make ott 
#	+make -C ./llvm_op

ott: main.pdf ssa_static.vo ssa_dynamic.vo ssa_wf.vo opsem_conv.vo \
	opsem_pp.vo ssa_interpreter.vo

assoclist.vo : assoclist.v
	$(COQC) $(COQARG) assoclist.v

ssa_coq_lib.vo : ssa_coq_lib.v ssa_def.vo assoclist.vo ssa_analysis.vo
	$(COQC) $(COQARG) ssa_coq_lib.v

ssa_def.vo : ssa_def.v ./monads/monad.vo ./compcert/Floats.vo assoclist.vo
	$(COQC) $(COQARG) ssa_def.v

ssa_def.v : ssa_def.ott
	$(OTT) -coq_expand_list_types true -i ssa_def.ott -o ssa_def.v
	./fixott.py ssa_def.v

ssa_coq.ott : ssa_coq_lib.vo ssa_def.ott coq2ott.py 
	./coq2ott.py
	cp merge.ott ssa_coq.ott       

m_ssa_static.ott : ssa_static.ott spanlines.py
	./spanlines.py ssa_static.ott

ssa_lib.v ssa_static.v: ssa_def.ott ssa_coq_lib.vo ssa_coq.ott ssa_lib.ott \
	m_ssa_static.ott ./monads/monad.vo ssa_analysis.vo
	$(OTT) -merge false -coq_expand_list_types true \
            -i ssa_def.ott -o _tmp_ssa_def.v \
	    -i ssa_coq.ott -i ssa_lib.ott -o ssa_lib.v \
	    -i m_ssa_static.ott -o ssa_static.v
	rm _tmp_ssa_def.v
	./fixott.py ssa_lib.v
	./fixott.py ssa_static.v

ssa_lib.vo: ssa_lib.v
	$(COQC) $(COQARG) ssa_lib.v

ssa_static.vo: ssa_static.v ssa_lib.vo
	$(COQC) $(COQARG) ssa_static.v

ssa_wf.vo: ssa_static.vo ssa_props.vo ssa_wf.v
	$(COQC) $(COQARG) ssa_wf.v

tactics.vo: tactics.v
	$(COQC) $(COQARG) tactics.v

targetdata.vo: targetdata.v ssa_def.vo ssa_lib.vo
	$(COQC) $(COQARG) targetdata.v

trace.vo: trace.v
	$(COQC) $(COQARG) trace.v

ssa_analysis.vo: compcert/Kildall.vo ssa_analysis.v assoclist.vo
	$(COQC) $(COQARG) ssa_analysis.v

genericvalues.vo: ssa_def.vo ssa_lib.vo tactics.vo trace.vo genericvalues.v \
	assoclist.vo targetdata.vo compcert/Memory.vo
	$(COQC) $(COQARG) genericvalues.v

ssa_dynamic.vo: ssa_dynamic.v ssa_def.vo ssa_lib.vo tactics.vo trace.vo \
	genericvalues.vo assoclist.vo
	$(COQC) $(COQARG) ssa_dynamic.v

ssa_interpreter.vo: ssa_interpreter.v ssa_dynamic.vo ssa_def.vo ssa_lib.vo \
	tactics.vo trace.vo genericvalues.vo assoclist.vo
	$(COQC) $(COQARG) ssa_interpreter.v

ssa_props.vo: ssa_props.v ssa_def.vo ssa_lib.vo genericvalues.vo assoclist.vo \
	ssa_dynamic.vo
	$(COQC) $(COQARG) ssa_props.v

opsem_pp.vo: opsem_pp.v ssa_dynamic.vo ssa_def.vo ssa_lib.vo genericvalues.vo \
	assoclist.vo ssa_props.vo
	$(COQC) $(COQARG) opsem_pp.v

opsem_conv.vo: opsem_conv.v ssa_dynamic.vo ssa_def.vo ssa_lib.vo trace.vo
	$(COQC) $(COQARG) opsem_conv.v

ssa.tex: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott main.tex 
	$(OTT) -merge false -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
            ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott

main.pdf: ssa.tex main.tex macros.sty 
	pdflatex main.tex
	pdflatex main.tex

clean: 
	+make -C ./ott clean
	+make -C ./compcert clean
	+make -C ./monads clean	
	+make -C ./llvm_op clean
	rm -rf main.pdf main.log main.aux main.log ssa_def.v ssa_lib.v \
		ssa_static.vo *.vo *.glob merge.ott m_*.ott

