Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "../../../theory/metatheory".

Require Import ssa_dynamic.
Require Import trace.
Require Import Metatheory.
Require Import assoclist.
Require Import monad.
Require Import genericvalues.
Require Import ssa_mem.

Export LLVMopsem.

Definition interInsn (state:State) : option (State*trace) :=
(* Check if the stack is empty. *) 
match state with
| mkState Sys TD Ps nil gl Mem0 => None
| mkState Sys TD Ps ((mkEC F B cs tmn lc arg0 als)::EC) gl Mem0 =>
  (* If cs is nil, we check tmn, 
     otherwise, we check the first cmd in cs *)
  match cs with
  | nil => (* terminator *)
    match tmn with
    | insn_return rid RetTy Result =>
      (* the suspended stacks cannot be empty, and
          there must be a caller of the current function. *)
      match EC with
      | nil => None
      | (mkEC F' B' nil tmn' lc' arg' als')::EC'' => None
      | (mkEC F' B' (c'::cs') tmn' lc' arg' als')::EC'' =>
        (* there must be a caller of the current function. *)
        if (Instruction.isCallInst c') 
        then 
          do Mem' <- free_allocas Mem0 als;
             ret ((mkState Sys TD Ps ((mkEC F' B' cs' tmn' (returnUpdateLocals TD c' RetTy Result lc lc' gl) arg' als')::EC'') gl Mem'),
                  trace_nil)
        else None
      end
    | insn_return_void rid =>
      (* the suspended stacks cannot be empty, and
          there must be a caller of the current function. *)
      match EC with
      | nil => None
      | (mkEC F' B' nil tmn' lc' arg' als')::EC'' => None
      | (mkEC F' B' (c'::cs') tmn' lc' arg' als')::EC'' =>
        (* there must be a caller of the current function. *)
        if (Instruction.isCallInst c')
        then
          do Mem' <- free_allocas Mem0 als;
             ret ((mkState Sys TD Ps ((mkEC F' B' cs' tmn' lc' arg' als')::EC'') gl Mem'),
                  trace_nil)
        else None
      end
    | insn_br bid Cond l1 l2 =>
      (* read the value of Cond *)
      do cond0 <- (getOperandInt TD 1 Cond lc gl);
      (* look up the target block *)
        match (if (cond0:nat)
               then lookupBlockViaLabelFromFdef F l1
               else lookupBlockViaLabelFromFdef F l2) with
        | None => None
        | Some (block_intro l' ps' cs' tmn') =>
            Some ((mkState Sys TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' 
                     (switchToNewBasicBlock (block_intro l' ps' cs' tmn') B lc) arg0 als)::EC) gl Mem0),
                  trace_nil)
        end
    | insn_br_uncond bid l0 =>
      (* look up the target block *)
      match (lookupBlockViaLabelFromFdef F l0) with
      | None => None
      | Some (block_intro l' ps' cs' tmn') =>
          Some ((mkState Sys TD Ps ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' 
                        (switchToNewBasicBlock (block_intro l' ps' cs' tmn') B lc) arg0 als)::EC) gl Mem0),
               trace_nil)
      end
    | insn_unreachable _ => None
    end

  | c::cs => (* non-terminator *)
    match c with
    | insn_bop id0 bop0 sz0 v1 v2 => 
      do gv3 <- BOP TD lc gl bop0 sz0 v1 v2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) arg0 als)::EC) gl Mem0),
              trace_nil)         
    | insn_extractvalue id0 t v idxs =>
      do gv <- getOperandValue TD v lc gl;
      do gv' <- extractGenericValue TD t gv idxs;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv') arg0 als)::EC) gl Mem0),
              trace_nil)
    | insn_insertvalue id0 t v t' v' idxs =>
      do gv <- getOperandValue TD v lc gl;
      do gv' <- getOperandValue TD v' lc gl;
      do gv'' <- insertGenericValue TD t gv idxs t' gv';
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv'') arg0 als)::EC) gl Mem0),
             trace_nil)
    | insn_malloc id0 t sz0 align0 =>
      do tsz <- getTypeAllocSize TD t;
      match (malloc TD Mem0 (tsz * sz0) align0) with
      | None => None
      | Some (Mem', mb) =>
        ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 (ptr2GV TD (mb, 0))) arg0 als)::EC) gl Mem'),
            trace_nil)
      end
    | insn_free fid t v =>
      do mptr <- getOperandPtr TD v lc gl;
      do Mem' <- free Mem0 mptr;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn lc arg0 als)::EC) gl Mem'), trace_nil)
    | insn_alloca id0 t sz0 align0 =>
      do tsz <- getTypeAllocSize TD t;
      match (malloc TD Mem0 (tsz * sz0) align0) with
      | None => None
      | Some (Mem', mb) =>
          ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 (ptr2GV TD (mb, 0))) arg0 (mb::als))::EC) gl Mem'),
              trace_nil)
      end
    | insn_load id0 t v align0 =>
      do mp <- getOperandPtr TD v lc gl;
      do gv <- mload TD Mem0 mp t align0;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv) arg0 als)::EC) gl Mem0),
              trace_nil)
    | insn_store sid t v1 v2 align0 =>
      do gv1 <- getOperandValue TD v1 lc gl;
      do mp2 <- getOperandPtr TD v2 lc gl;
      do Mem' <- mstore TD Mem0 mp2 t gv1 align0;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn lc arg0 als)::EC) gl Mem'),
             trace_nil)
    | insn_gep id0 inbounds0 t v idxs =>
      do mp <- getOperandPtr TD v lc gl;
      do mp' <- GEP TD lc gl t mp idxs inbounds0;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 (ptr2GV TD mp')) arg0 als)::EC) gl Mem0),
             trace_nil)
    | insn_ext id0 extop0 t1 v1 t2 =>
      do gv2 <- EXT TD lc gl extop0 t1 v1 t2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2) arg0 als)::EC) gl Mem0),
             trace_nil)
    | insn_cast id0 castop0 t1 v1 t2 =>
      do gv2 <- CAST TD lc gl castop0 t1 v1 t2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2) arg0 als)::EC) gl Mem0),
             trace_nil)
    | insn_icmp id0 cond0 t v1 v2 =>
      do gv3 <- ICMP TD lc gl cond0 t v1 v2;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) arg0 als)::EC) gl Mem0),
             trace_nil)
    | insn_select id0 v0 t v1 v2 =>
      do cond0 <- getOperandInt TD 1 v0 lc gl;
      do gv1 <- getOperandValue TD v1 lc gl;
      do gv2 <- getOperandValue TD v2 lc gl;
         ret ((mkState Sys TD Ps ((mkEC F B cs tmn (if (cond0:nat) then updateAddAL _ lc id0 gv2 else updateAddAL _ lc id0 gv1) arg0 als)::EC) gl Mem0),
             trace_nil)  
    | insn_call rid noret0 tailc0 rt fid lp =>
      (* only look up the current module for the time being, 
         do not support linkage. *)
      match (lookupFdefViaIDFromProducts Ps fid) with
      | None => None
      | Some (fdef_intro (fheader_intro rt' fid' la) lb) =>
        if id_dec fid fid' then
          if typ_dec rt rt' then
            match (getEntryBlock (fdef_intro (fheader_intro rt fid la) lb)) with
            | None => None
            | Some (block_intro l' ps' cs' tmn') =>
                ret ((mkState Sys TD Ps ((mkEC (fdef_intro (fheader_intro rt fid la) lb) 
                                          (block_intro l' ps' cs' tmn') cs' tmn' (initLocals la (params2GVs TD lp lc gl)) 
                                          (params2GVs TD lp lc gl) nil)::
                                        (mkEC F B ((insn_call rid noret0 tailc0 rt fid lp)::cs) tmn lc arg0 als)::EC) gl Mem0),
                    trace_nil)
            end
          else None
        else None
      end
    end
  end
end.

Lemma dsInsn__implies__interInsn : forall state state' tr,
  dsInsn state state' tr ->
  interInsn state = Some (state', tr).
Proof. 
  intros state state' tr HdsInsn.
  (dsInsn_cases (destruct HdsInsn) Case); simpl;
    try solve [rewrite H; simpl; rewrite H0; simpl; rewrite H1; simpl; auto |
               rewrite H; simpl; rewrite H0; simpl; auto |
               rewrite H; simpl; auto ].
  Case "dsBranch".
    rewrite H. simpl. rewrite <- H0. simpl. auto.
  Case "dsBranch_uncond".
    rewrite <- H. simpl. auto.
  Case "dsCall".
    rewrite H. simpl in H0. rewrite H0. 
    destruct (id_dec fid fid); auto.
      destruct (typ_dec rt rt); auto.
        contradict n; auto.
      contradict n; auto.
Qed.

Lemma interInsn__implies__dsInsn : forall state state' tr,
  interInsn state = Some (state', tr) ->
  dsInsn state state' tr.
Proof.
  intros state state' tr HinterInsn.
  destruct state.
  destruct ECS0; simpl in HinterInsn;
    try solve [inversion HinterInsn].

    destruct e as [F B cs tmn lc arg0 als].
    destruct cs.
      destruct tmn.
      Case "insn_return".
        destruct ECS0;
          try solve [inversion HinterInsn].
          
          destruct e as [F' B' cs' tmn' lc' arg' als'].
          destruct cs';
            try solve [inversion HinterInsn].

            remember (Instruction.isCallInst c) as R1.
            remember (free_allocas Mem0 als) as R2.
            destruct R1; try solve [inversion HinterInsn].
            destruct R2; inversion HinterInsn; subst; eauto.

      Case "insn_return_void".
        destruct ECS0;
          try solve [inversion HinterInsn].
          
          destruct e as [F' B' cs' tmn' lc' arg' als'].
          destruct cs';
            try solve [inversion HinterInsn].

            remember (Instruction.isCallInst c) as R1.
            remember (free_allocas Mem0 als) as R2.
            destruct R1; try solve [inversion HinterInsn].
            destruct R2; inversion HinterInsn; subst; eauto.

      Case "insn_br".
        remember (getOperandInt CurTargetData0 1 v lc Globals0) as R1.
        destruct R1; try solve [inversion HinterInsn].
          simpl in HinterInsn.
          destruct n.
            remember (lookupBlockViaLabelFromFdef F l0) as R2.
            destruct R2; inversion HinterInsn; subst.
              destruct b.
              inversion HinterInsn; subst; eauto.
        
            remember (lookupBlockViaLabelFromFdef F l1) as R2.
            destruct R2; inversion HinterInsn; subst.
              destruct b.
              inversion HinterInsn; subst; eauto.

      Case "insn_br_uncond".
        remember (lookupBlockViaLabelFromFdef F l0) as R2.
        destruct R2; inversion HinterInsn; subst.
          destruct b.
          inversion HinterInsn; subst; eauto.

      Case "insn_unreachable".
        inversion HinterInsn.
                    
      destruct c.
      Case "insn_bop".
        remember (BOP CurTargetData0 lc Globals0 b s v v0) as R1.
        destruct R1; 
          simpl in HinterInsn;
          inversion HinterInsn; subst; eauto.
          
      Case "insn_extractvalue".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (extractGenericValue CurTargetData0 t g l0) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_insertvalue".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (insertGenericValue CurTargetData0 t g l0 t0 g0) as R3.
        destruct R3; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_malloc".
        remember (getTypeAllocSize CurTargetData0 t) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (malloc CurTargetData0 Mem0 (n*s) a) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        destruct p; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_free".
        remember (getOperandPtr CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (free Mem0 m) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_alloca".
        remember (getTypeAllocSize CurTargetData0 t) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (malloc CurTargetData0 Mem0 (n*s) a) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        destruct p; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_load".
        remember (getOperandPtr CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (mload CurTargetData0 Mem0 m t a) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_store".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandPtr CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (mstore CurTargetData0 Mem0 m t g a) as R3.
        destruct R3; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.
          
      Case "insn_gep".
        remember (getOperandPtr CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (GEP CurTargetData0 lc Globals0 t m l0 i1) as R2.
        destruct R2; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_ext".
        remember (EXT CurTargetData0 lc Globals0 e t v t0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_cast".
        remember (CAST CurTargetData0 lc Globals0 c t v t0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_icmp".
        remember (ICMP CurTargetData0 lc Globals0 c t v v0) as R.
        destruct R; simpl in HinterInsn; 
          inversion HinterInsn; subst; eauto.

      Case "insn_select".
        remember (getOperandInt CurTargetData0 1 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v1 lc Globals0) as R3.
        destruct R3; simpl in HinterInsn; 
          try solve [inversion HinterInsn].
        inversion HinterInsn; subst; eauto.

      Case "insn_call".
        remember (lookupFdefViaIDFromProducts CurProducts0 i1) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].
        destruct f. destruct f.
        destruct (id_dec i1 i2); try solve [inversion HinterInsn]; subst.
        destruct (typ_dec t0 t1); try solve [inversion HinterInsn]; subst.
        destruct b; try solve [inversion HinterInsn].
        destruct b.
        inversion HinterInsn; subst; eauto.
Qed.

Extraction interInsn.


