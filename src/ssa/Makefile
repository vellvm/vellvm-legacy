OTT=ott
COQC=coqc
COQARG=-I ./ott -I ./monads -I ../../../theory/metatheory/

all:
	+make -C ./monads
	+make -C ./ott
	+make ott 
	+make -C ./llvm_op

ott: main.pdf ssa.vo ssa_dynamic.vo opsem_conv.vo opsem_pp.vo

assoclist.vo : assoclist.v
	$(COQC) $(COQARG) assoclist.v

ssa_coq_lib.vo : ssa_coq_lib.v ssa_def.vo assoclist.vo
	$(COQC) $(COQARG) ssa_coq_lib.v

ssa_def.vo : ssa_def.v ./monads/monad.vo
	$(COQC) $(COQARG) ssa_def.v

ssa_def.v : ssa_def.ott emacs.ott
	ott -coq_expand_list_types true -i ssa_def.ott -i emacs.ott -o ssa_def.v

ssa_coq.ott : ssa_coq_lib.vo ssa_def.ott coq2ott.py 
	./coq2ott.py
	cp merge.ott ssa_coq.ott       

m_ssa_static.ott : ssa_static.ott spanlines.py
	./spanlines.py ssa_static.ott

ssa.v: ssa_def.ott ssa_coq_lib.vo ssa_coq.ott ssa_lib.ott m_ssa_static.ott emacs.ott ./monads/monad.vo
	ott -merge false -coq_expand_list_types true \
            -i ssa_def.ott -i ssa_coq.ott -i ssa_lib.ott -i m_ssa_static.ott -i emacs.ott -o ssa.v

ssa.vo: ssa.v
	$(COQC) $(COQARG) ssa.v

tactics.vo: tactics.v
	$(COQC) tactics.v

targetdata.vo: targetdata.v ssa.vo
	$(COQC) $(COQARG) targetdata.v

ssa_mem.vo: ssa_mem.v ssa.vo tactics.vo targetdata.vo
	$(COQC) $(COQARG) ssa_mem.v

trace.vo: trace.v
	$(COQC) trace.v

genericvalues.vo: ssa.vo tactics.vo ssa_mem.vo trace.vo genericvalues.v assoclist.vo
	$(COQC) $(COQARG) genericvalues.v

ssa_dynamic.vo: ssa_dynamic.v ssa.vo tactics.vo ssa_mem.vo trace.vo genericvalues.vo assoclist.vo
	$(COQC) $(COQARG) ssa_dynamic.v

ssa_props.vo: ssa_props.v ssa.vo genericvalues.vo assoclist.vo
	$(COQC) $(COQARG) ssa_props.v

opsem_pp.vo: opsem_pp.v ssa_dynamic.vo ssa.vo ssa_mem.vo genericvalues.vo assoclist.vo ssa_props.vo
	$(COQC) $(COQARG) opsem_pp.v

opsem_conv.vo: opsem_conv.v ssa_dynamic.vo ssa.vo trace.vo
	$(COQC) $(COQARG) opsem_conv.v

ssa.tex: ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott omain.tex 
	$(OTT) -merge false -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ssa_def.ott ssa_coq.ott ssa_lib.ott m_ssa_static.ott

main.pdf: ssa.tex main.tex macros.sty 
	pdflatex main.tex
	pdflatex main.tex

clean: 
	+make -C ./ott clean
	+make -C ./monads clean	
	+make -C ./llvm_op clean
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_def.v ssa.v *.vo *.glob merge.ott m_*.ott

