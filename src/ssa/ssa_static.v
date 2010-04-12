Require Import ssa_lib.
Require Import List.
Require Import ListSet.
Require Import Monad.
Require Import Logic_Type.
Require Import reflect.

(* defns Jwf_typ *)
Inductive wf_typ : typ -> Prop :=    (* defn wf_typ *)
 | wf_typ_int : forall (N5:INT),
     wf_typ (typ_int N5)
 | wf_typ_metadate : 
     wf_typ typ_metadata
 | wf_typ_function : forall (typ_list:list typ) (typ_5:typ),
     isValidReturnTyp typ_5 ->
     wf_typ typ_5 ->
     (forall typ_, In typ_ typ_list -> (isValidArgumentTyp typ_)) ->
     (forall typ_, In typ_ typ_list -> (wf_typ typ_)) ->
     wf_typ (typ_function typ_5 typ_list).

(* defns Jwf_operand_insn *)
Definition wf_operand_insn (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef_info5:fdef_info)
                           (block5:block)
                           (insn5 insn':insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  monad2prop _ (
  do id' <- (getInsnID  insn');
  do OpBlock <- (lookupBlockViaIDFromFdefC fdef5 id');

  (* Check that a definition dominates all of its uses *)
  do If (isInvokeInsnB insn')
     then 
     (* Invoke results are only usable in the normal destination, not in the
        exceptional destination. *)
     do ln <- getNormalDestFromInvokeInsnC insn';
     do NormalDest <- lookupBlockViaLabelFromSystem system5 ln;
     do lu <- getUnwindDestFromInvokeInsnC insn';
     do UnwindDest <- lookupBlockViaLabelFromSystem system5 lu;
     do ret (not (NormalDest = UnwindDest));

     (* PHI nodes differ from other nodes because they actually "use" the
        value in the predecessor basic blocks they correspond to. *)
     do UseBlock <- 
        If (isPhiNodeB insn5) 
        then 
        do l <- getLabelViaIDFromPhiNode insn5 id';
           lookupBlockViaLabelFromSystem system5 l
        else
           ret block5
        endif;
        If (isPhiNodeB insn5 && blockEqB UseBlock OpBlock)
        then
        (* Special case of a phi node in the normal destination or the unwind
           destination *)
           ret (block5 = NormalDest /\ isReachableFromEntry fdef_info5 UseBlock)
        else
        (* Invoke result does dominate all uses! *)
        do ret (blockDominates dt5 NormalDest UseBlock \/ 
                ~ (isReachableFromEntry fdef_info5 UseBlock));

        (* If the normal successor of an invoke instruction has multiple
           predecessors, then the normal edge from the invoke is critical,
           so the invoke value can only be live if the destination block
           dominates all of it's predecessors (other than the invoke). *)
           If (negb (hasSinglePredecessor NormalDest usedef_block5) &&
               (isReachableFromEntryB fdef_info5 UseBlock)
              )
           then
           (* If it is used by something non-phi, then the other case is that
              'NormalDest' dominates all of its predecessors other than the
              invoke.  In this case, the invoke value can still be used. *)
             for PI in (predOfBlock NormalDest usedef_block5) do
               (* Invoke result must dominate all uses! *)
               If (insnHasParent insn' system5)
               then
               do parentOfInsn' <- getParentOfInsnFromSystemC insn' system5;
                  If (negb (blockDominatesB dt5 NormalDest PI) && 
                      isReachableFromEntryB fdef_info5 PI)
                  then ret False
                  endif
               else
                  ret True
               endif
             endfor
           endif
        endif
     else If (isPhiNodeB insn5)
     then
     (* PHI nodes are more difficult than other nodes because they actually
        "use" the value in the predecessor basic blocks they correspond to. *)
     do predl <- getLabelViaIDFromPhiNode insn5 id';
     do PredBB <- lookupBlockViaLabelFromSystem system5 predl;
        (* Instruction must dominate all uses! *) 
        ret (blockDominates dt5 OpBlock PredBB \/ ~ isReachableFromEntry fdef_info5 PredBB)
     else       
     do If (blockEqB OpBlock block5)
        then
          (* If they are in the same basic block, make sure that the definition
             comes before the use. *)
          ret (insnDominates insn' insn5 \/ ~ isReachableFromEntry fdef_info5 block5)
        endif;
        (* Definition must dominate use unless use is unreachable! *)
        ret (insnDominates insn' insn5 \/ ~ isReachableFromEntry fdef_info5 block5)
        (* !! FIXME
          Assert2(InstsInThisBlock.count(Op) || DT->dominates(Op, &I) ||
                  !DT->isReachableFromEntry(BB),
                  "Instruction does not dominate all uses!", Op, &I);
          *)
     endif endif;
     ret True
  ).

(* defns Jwf_operand *)
Definition wf_operand (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef_info5:fdef_info)
                            (block5:block)
                            (insn5:insn) 
                            (id':id): Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  monad2prop _ (
  do ret (insnInSystemModuleFdefBlock 
            insn5 
            system5  
            ( module5 , ( usedef_insn5 ,  usedef_block5 )) 
            ( fdef5 ,  dt5 )   
            block5);
  do ids5 <- ret (getInsnOperandsC insn5);
  do ret ( set_In  id' ids5 );

  do id_binding' <- ret (lookupBindingViaIDFromSystemC system5 id');
  (* Check to make sure that only first-class-values are operands to instructions. *)
  do typ' <- (getBindingTypC id_binding');
  do ret (isFirstClassTyp typ');
  
  (* Valid use of metadata pointer. *)
  do If (isPointerTypB typ')
     then 
     do typ'' <- (getPointerEltTypC typ');
        ret (not (typEq typ'' typ_metadata))
     endif;

  do If (isBindingFdecB id_binding')
     then
     do fdec5 <- (getBindingFdecC id_binding');
     (* Check to make sure that the "address of" an intrinsic function is never
        taken *)
     do id0 <- ret (getFdecIDC fdec5);
     do ret (( ~ set_In id0 intrinsic_funs5) \/  getCallName insn5 id0);

     (* Referencing function exists in current module *)
        ret (In  (product_function_dec fdec5) module5)
     endif;

  do If (isBindingArgB id_binding')
     then 
     do arg <- getBindingArgC id_binding';
     (* Referring to an argument in the current function *)
        ret (argInFdef arg fdef5)
     endif;
(*
  do If (isBindingGB id_binding')
     then 
     (* Referencing global in the current module *)
     do g <- getBindingGC id_binding';
        ret True
     endif
*)        
     
  do If (isBindingInsnB id_binding')
     then 
     (*  Check when id_binding' is insn *)
     do insn' <- getBindingInsnC id_binding';
        ret (wf_operand_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 insn')
     endif;

     ret True
  ).
  
(* defns Jwf_label *)
Inductive wf_label : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> l -> Prop :=    (* defn wf_label *)
 | wf_label_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef5:fdef) (dt5:dt) (block5:block) (insn5:insn) (l5:l) (ls5:ls),
     insnInSystemModuleFdefBlock insn5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 ->
     getInsnLabels insn5 ls5 ->
      ( set_In  l5   ls5 )  ->
      (lookupBlockViaLabelFromSystem  system5   l5  =   (Some  block5 )  )  ->
     blockInFdef block5 fdef5 ->
     wf_label intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 insn5 l5.

(* defns Jwf_insn_base *)
Definition wf_insn_base (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef_info5:fdef_info)
                            (block5:block)
                            (insn5:insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  monad2prop _ (
  (* Instruction must be embedded in basic block! *)
  do ret (insnInSystemModuleFdefBlock 
            insn5   
            system5   
            ( module5 , ( usedef_insn5 ,  usedef_block5 ))     
            ( fdef5 ,  dt5 )   
            block5);

  (* Check that non-phi nodes are not self referential *)
  do If (isPhiNodeB insn5)
     then 
       for insn in (getInsnUseDef usedef_insn5 insn5) do
         ret ((not (getInsnID insn5 = getInsnID insn)) \/ 
              (isReachableFromEntry (fdef5, dt5) block5))
       endfor
     endif;

  (* Verify that if this is a terminator that it is at the end of the block. *)
  do If (isTerminatorInsnB insn5)
     then 
     do insn' <- (getTerminator block5);
        ret (getInsnID insn5 = getInsnID insn')
     endif;

  (* Check that void typed values don't have names 
     We dont need to check this in Coq. *)

  (* Check that the return value of the instruction is either void or a legal
     value type. *)
  do typ5 <- (getInsnTypC insn5);
  do ret (typEq typ5 typ_void  \/  isFirstClassTyp typ5);

  (* Check that the instruction doesn't produce metadata or metadata*. Calls
     all already checked against the callee type. *)
  do ret ((not (typEq typ5 typ_metadata ))   \/  
          isInvokeInsn insn5   \/  
          isCallInsn insn5 );

  (* Instructions may not produce pointer to metadata *)
  do If (isPointerTypB typ5 )
     then  
     do typ' <- (getPointerEltTypC typ5);
        ret (not (typEq typ' typ_metadata ))
     endif;

  (* Check that all uses of the instruction, if they are instructions
     themselves, actually have parent basic blocks.  If the use is not an
     instruction, it is an error!
     We should prove a lemma for this later *)
  
  (* Check operands *)
  do for insn in (getInsnOperandsC insn5) do
     (* Check to make sure that only first-class-values are operands to
        instructions. *)
       ret (wf_operand intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 insn)
     endfor;

  (* Check labels *)
  do for l in (getInsnLabelsC insn5) do
       ret (wf_label intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 l)
     endfor;

     ret True
  ).

(* defns Jwf_insn *)
Inductive wf_insn : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> Prop :=    (* defn wf_insn *)
 | wf_insn_return : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block) (typ5:typ) (value5:value),
     wf_insn_base intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_return typ5 value5) ->
     getReturnTyp fdef5 typ5 ->
      (not ( typEq typ5 typ_void ))  ->
     wf_insn intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_return typ5 value5)
 | wf_insn_return_void : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block),
     wf_insn intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 insn_return_void ->
     getReturnTyp fdef5 typ_void ->
     wf_insn intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 insn_return_void
 | wf_insn_br : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef_info5:fdef_info) (block5:block) (typ5:typ) (value5:value) (l1 l2:l) (dt5:dt),
     wf_insn_base intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_br typ5 value5 l1 l2) ->
      (blockDominates  dt5   block5   block5 )  ->
      (insnDominates   insn_return_void     insn_return_void  )  ->
     wf_insn intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   fdef_info5 block5 (insn_br typ5 value5 l1 l2).

(* defns Jwf_list_insn *)
Inductive wf_list_insn : intrinsic_funs -> system -> module_info -> fdef_info -> block -> list_insn -> Prop :=    (* defn wf_list_insn *)
 | wf_list_insn_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (block5:block),
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5  nil 
 | wf_list_insn_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (block5:block) (list_insn5:list_insn) (insn5:insn),
     wf_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 ->
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 list_insn5 ->
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5  ( insn5 :: list_insn5 ) .

(* defns Jwf_block *)
Inductive wf_block : intrinsic_funs -> system -> module_info -> fdef_info -> block -> Prop :=    (* defn wf_block *)
 | wf_block_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (block5:block) (l5:l) (list_insn5:list_insn),
     blockInSystemModuleFdef  (block_intro l5 list_insn5)  system5 module_info5 fdef_info5 ->
     getInsnsFromBlock block5 list_insn5 ->
     wf_list_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 list_insn5 ->
     insnsChecksTerminatorInsn list_insn5 ->
     insnsStartsWithPhiNode list_insn5 ->
     wf_block intrinsic_funs5 system5 module_info5 fdef_info5 block5.

(* defns Jwf_list_block *)
Inductive wf_list_block : intrinsic_funs -> system -> module_info -> fdef_info -> list_block -> Prop :=    (* defn wf_list_block *)
 | wf_list_block_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info),
     wf_list_block intrinsic_funs5 system5 module_info5 fdef_info5  nil 
 | wf_list_block_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef_info5:fdef_info) (list_block5:list_block) (block5:block),
     wf_block intrinsic_funs5 system5 module_info5 fdef_info5 block5 ->
     wf_list_block intrinsic_funs5 system5 module_info5 fdef_info5 list_block5 ->
     wf_list_block intrinsic_funs5 system5 module_info5 fdef_info5  ( block5 :: list_block5 ) .

(* defns Jwf_fdef *)
Inductive wf_fdef : intrinsic_funs -> system -> module_info -> fdef -> Prop :=    (* defn wf_fdef *)
 | wf_fdef_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fheader5:fheader) (list_block5:list_block) (dt5:dt),
     productInSystemModule (product_function_def  (fdef_intro fheader5 list_block5) ) system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   ->
     genDominatorTree (fdef_intro fheader5 list_block5) module5 = dt5  ->
     wf_list_block intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( (fdef_intro fheader5 list_block5) ,  dt5 )   list_block5 ->
     wf_fdef intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   (fdef_intro fheader5 list_block5).

(* defns Jwf_prod *)
Inductive wf_prod : intrinsic_funs -> system -> module_info -> product -> Prop :=    (* defn wf_prod *)
 | wf_prod_function_dec : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdec5:fdec),
     wf_prod intrinsic_funs5 system5 module_info5 (product_function_dec fdec5)
 | wf_prod_function_def : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef),
     wf_fdef intrinsic_funs5 system5 module_info5 fdef5 ->
     wf_prod intrinsic_funs5 system5 module_info5 (product_function_def fdef5).

(* defns Jwf_prods *)
Inductive wf_prods : intrinsic_funs -> system -> module_info -> list_product -> Prop :=    (* defn wf_prods *)
 | wf_prods_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info),
     wf_prods intrinsic_funs5 system5 module_info5  nil 
 | wf_prods_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (list_product5:list_product) (product5:product),
     wf_prods intrinsic_funs5 system5 module_info5 list_product5 ->
     wf_prod intrinsic_funs5 system5 module_info5 product5 ->
     wf_prods intrinsic_funs5 system5 module_info5  ( product5 :: list_product5 ) .

(* defns Jwf_module *)
Inductive wf_module : intrinsic_funs -> system -> module -> Prop :=    (* defn wf_module *)
 | wf_module_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (list_product5:list_product) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block),
      In   list_product5    system5  ->
     genInsnUseDef  list_product5  = usedef_insn5  ->
     genBlockUseDef  list_product5  = usedef_block5  ->
     wf_prods intrinsic_funs5 system5   (  list_product5  , ( usedef_insn5 ,  usedef_block5 ))   list_product5 ->
     wf_module intrinsic_funs5 system5  list_product5 .

(* defns Jwf_list_module *)
Inductive wf_list_module : intrinsic_funs -> system -> list_module -> Prop :=    (* defn wf_list_module *)
 | wf_list_module_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system),
     wf_list_module intrinsic_funs5 system5  nil 
 | wf_list_module_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (list_module5:list_module) (module5:module),
     wf_module intrinsic_funs5 system5 module5 ->
     wf_list_module intrinsic_funs5 system5 list_module5 ->
     wf_list_module intrinsic_funs5 system5  ( module5 :: list_module5 ) .

(* defns Jwf_system *)
Inductive wf_system : intrinsic_funs -> system -> Prop :=    (* defn wf_system *)
 | wf_system_intro : forall (intrinsic_funs5:intrinsic_funs) (list_module5:list_module),
     wf_list_module intrinsic_funs5  list_module5  list_module5 ->
     uniqSystem  list_module5  ->
     wf_system intrinsic_funs5  list_module5 .

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./monads" "-I" "./ott") ***
*** End: ***
 *)

