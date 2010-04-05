Require Import ssa_lib.
Require Import List.
Require Import ListSet.
Require Import Monad.
Require Import Logic_Type.

(* defns Jwf_typ *)
Inductive wf_typ : typ -> Prop :=    (* defn wf_typ *)
 | wf_typ_int : forall (N5:N),
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
Inductive wf_operand_insn : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> insn -> Prop :=    (* defn wf_operand_insn *)
 | wf_operand_insn_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block) (insn5 insn':insn) (id':id) (block':block) (l1 l2 l'':l) (block'':block),
      (getInsnID  insn'  =   (Some  id' )  )  ->
     lookupBlockViaIDFromFdef fdef5 id'  (Some  block' )  ->
      (  ( isInvokeInsn insn' )   ->    getNormalDestFromInvokeInsn insn' l1  ->  getUnwindDestFromInvokeInsn insn' l2   ->   (not (  l1  =  l2  ))   ) /\ ((~  ( isInvokeInsn insn' )  ) ->   True  )  ->
       ( isPhiNode insn5 )   ->   (   getLabelViaIDPhiNode insn5 id'  (Some  l'' )   /\   (lookupBlockViaLabelFromSystem  system5   l''  =   (Some  block'' )  )    /\   (   (  (blockDominates  dt5   block'   block'' )  )   \/   (  (not (  (  (isReachableFromEntry    ( fdef5 ,  dt5 )     block5 )  )  ))  )   )   )   ->
       (  (notT ( isPhiNode insn5 ))  )   ->   (   (insnDominates  insn'   insn5 )   \/   (  (not (  (  (isReachableFromEntry    ( fdef5 ,  dt5 )     block5 )  )  ))  )   )   ->
     wf_operand_insn intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 insn5 insn'.

(* defns Jwf_operand *)
Inductive wf_operand : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> id -> Prop :=    (* defn wf_operand *)
 | wf_operand_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef5:fdef) (dt5:dt) (block5:block) (insn5:insn) (id':id) (ids5:ids) (id_binding':id_binding) (typ' typ'':typ) (fdec5:fdec) (id0:id) (arg5:arg) (insn':insn) (module_info5:module_info) (fdef_info5:fdef_info),
     insnInSystemModuleFdefBlock insn5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 ->
     getInsnOperands insn5 ids5 ->
      ( set_In  id'   ids5 )  ->
     lookupBindingViaIDFromSystem system5 id' id_binding' ->
     getBindingTyp id_binding'  (Some  typ' )  ->
     isFirstClassTyp typ' ->
       ( getPointerEltTyp typ' typ'' )   ->   (  (not ( typeEq typ'' typ_metadata ))  )   ->
       ( isBindingFdec id_binding' fdec5 )   ->   (   getFdecID fdec5 id0  /\   (   ( ~ set_In  id0   intrinsic_funs5 )   \/  getCallName insn5 id0  )    /\   In  (product_function_dec fdec5)   module5   )   ->
       ( isBindingArg id_binding' arg5 )   ->   ( argInFdef arg5 fdef5 )   ->
       ( isBindingInsn id_binding' insn' )   ->   ( wf_operand_insn intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn5 insn' )   ->
     wf_operand intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 insn5 id'.

(* defns Jwf_label *)
Inductive wf_label : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> l -> Prop :=    (* defn wf_label *)
 | wf_label_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef5:fdef) (dt5:dt) (block5:block) (insn5:insn) (l5:l) (ls5:ls),
     insnInSystemModuleFdefBlock insn5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 ->
     getInsnLabels insn5 ls5 ->
      ( set_In  l5   ls5 )  ->
      (lookupBlockViaLabelFromSystem  system5   l5  =   (Some  block5 )  )  ->
     blockInFdef block5 fdef5 ->
     wf_label intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 insn5 l5.

Fixpoint nonPhiNodes_arent_selfRef (list_insn5:list_insn) (fdef5:fdef) (dt5:dt) (block5:block) (insn5:insn): Prop :=
match list_insn5 with
| nil => True
| insn_ :: list_insn5' => 
  ((not ( getInsnID insn5 = getInsnID insn_ ) )   \/   
   (isReachableFromEntry ( fdef5 , dt5 ) block5 ) ) /\
  nonPhiNodes_arent_selfRef list_insn5' fdef5 dt5 block5 insn5
end.

Definition visitInstruction (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef_info5:fdef_info)
                            (block5:block)
                            (insn5:insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let (fdef5, dt5) := fdef_info5 in 
  monad2prop _ (
  (* Instruction must be embedded in basic block! *)
  do ret 
  (insnInSystemModuleFdefBlock 
    insn5   
    system5   
    ( module5 , ( usedef_insn5 ,  usedef_block5 ))     
    ( fdef5 ,  dt5 )   
    block5);
  (* Check that non-phi nodes are not self referential *)
  do If (isPhiNodeS insn5)
     then 
     do list_insn5 <- ret (getInsnUseDef  usedef_insn5 insn5);
        ret (nonPhiNodes_arent_selfRef list_insn5 fdef5 dt5 block5 insn5)
     endif;
     ret True
  ).

(*
/// verifyInstruction - Verify that an instruction is well formed.
///
void Verifier::visitInstruction(Instruction &I) {  
  BasicBlock *BB = I.getParent();
  Assert1(BB, "Instruction not embedded in basic block!", &I);

  if (!isa<PHINode>(I)) {   // Check that non-phi nodes are not self referential
    for (Value::use_iterator UI = I.use_begin(), UE = I.use_end();
         UI != UE; ++UI)
      Assert1( *UI != (User* )&I || !DT->isReachableFromEntry(BB),
              "Only PHI nodes may reference their own value!", &I);
  }

  // Verify that if this is a terminator that it is at the end of the block.
  if (isa<TerminatorInst>(I))
    Assert1(BB->getTerminator() == &I, "Terminator not at end of block!", &I);

  // Check that void typed values don't have names
  Assert1(I.getType() != Type::getVoidTy(I.getContext()) || !I.hasName(),
          "Instruction has a name, but provides a void value!", &I);

  // Check that the return value of the instruction is either void or a legal
  // value type.
  Assert1(I.getType() == Type::getVoidTy(I.getContext()) ||
          I.getType()->isFirstClassType()
          || ((isa<CallInst>(I) || isa<InvokeInst>(I))
              && isa<StructType>(I.getType())),
          "Instruction returns a non-scalar type!", &I);

  // Check that the instruction doesn't produce metadata or metadata*. Calls
  // all already checked against the callee type.
  Assert1(I.getType() != Type::getMetadataTy(I.getContext()) ||
          isa<CallInst>(I) || isa<InvokeInst>(I),

 if (const PointerType *PTy = dyn_cast<PointerType>(I.getType()))
    Assert1(PTy->getElementType() != Type::getMetadataTy(I.getContext()),
            "Instructions may not produce pointer to metadata.", &I);


  // Check that all uses of the instruction, if they are instructions
  // themselves, actually have parent basic blocks.  If the use is not an
  // instruction, it is an error!
  for (User::use_iterator UI = I.use_begin(), UE = I.use_end();
       UI != UE; ++UI) {
    Assert1(isa<Instruction>( *UI), "Use of instruction is not an instruction!",
            *UI);
    Instruction *Used = cast<Instruction>( *UI);
    Assert2(Used->getParent() != 0, "Instruction referencing instruction not"
            " embedded in a basic block!", &I, Used);
  }

  for (unsigned i = 0, e = I.getNumOperands(); i != e; ++i) {
    Assert1(I.getOperand(i) != 0, "Instruction has null operand!", &I);

    // Check to make sure that only first-class-values are operands to
    // instructions.
    if (!I.getOperand(i)->getType()->isFirstClassType()) {
      Assert1(0, "Instruction operands must be first-class values!", &I);
    }

    if (const PointerType *PTy =
            dyn_cast<PointerType>(I.getOperand(i)->getType()))
      Assert1(PTy->getElementType() != Type::getMetadataTy(I.getContext()),
              "Invalid use of metadata pointer.", &I);
    if (Function *F = dyn_cast<Function>(I.getOperand(i))) {
      // Check to make sure that the "address of" an intrinsic function is never
      // taken.
      Assert1(!F->isIntrinsic() || (i == 0 && isa<CallInst>(I)),
              "Cannot take the address of an intrinsic!", &I);
      Assert1(F->getParent() == Mod, "Referencing function in another module!",
              &I);
    } else if (BasicBlock *OpBB = dyn_cast<BasicBlock>(I.getOperand(i))) {
      Assert1(OpBB->getParent() == BB->getParent(),
              "Referring to a basic block in another function!", &I);
    } else if (Argument *OpArg = dyn_cast<Argument>(I.getOperand(i))) {
      Assert1(OpArg->getParent() == BB->getParent(),
              "Referring to an argument in another function!", &I);
    } else if (GlobalValue *GV = dyn_cast<GlobalValue>(I.getOperand(i))) {
      Assert1(GV->getParent() == Mod, "Referencing global in another module!",
              &I);
    } else if (Instruction *Op = dyn_cast<Instruction>(I.getOperand(i))) {
      BasicBlock *OpBlock = Op->getParent();

      // Check that a definition dominates all of its uses.
      if (InvokeInst *II = dyn_cast<InvokeInst>(Op)) {
        // Invoke results are only usable in the normal destination, not in the
        // exceptional destination.
        BasicBlock *NormalDest = II->getNormalDest();

        Assert2(NormalDest != II->getUnwindDest(),
                "No uses of invoke possible due to dominance structure!",
                Op, &I);

        // PHI nodes differ from other nodes because they actually "use" the
        // value in the predecessor basic blocks they correspond to.
        BasicBlock *UseBlock = BB;
        if (isa<PHINode>(I))
          UseBlock = cast<BasicBlock>(I.getOperand(i+1));

        if (isa<PHINode>(I) && UseBlock == OpBlock) {
          // Special case of a phi node in the normal destination or the unwind
          // destination.
          Assert2(BB == NormalDest || !DT->isReachableFromEntry(UseBlock),
                  "Invoke result not available in the unwind destination!",
                  Op, &I);
        } else {
          Assert2(DT->dominates(NormalDest, UseBlock) ||
                  !DT->isReachableFromEntry(UseBlock),
                  "Invoke result does not dominate all uses!", Op, &I);

          // If the normal successor of an invoke instruction has multiple
          // predecessors, then the normal edge from the invoke is critical,
          // so the invoke value can only be live if the destination block
          // dominates all of it's predecessors (other than the invoke).
          if (!NormalDest->getSinglePredecessor() &&
              DT->isReachableFromEntry(UseBlock))
            // If it is used by something non-phi, then the other case is that
            // 'NormalDest' dominates all of its predecessors other than the
            // invoke.  In this case, the invoke value can still be used.
            for (pred_iterator PI = pred_begin(NormalDest),
                 E = pred_end(NormalDest); PI != E; ++PI)
              if ( *PI != II->getParent() && !DT->dominates(NormalDest, *PI) &&
                  DT->isReachableFromEntry( *PI)) {
                CheckFailed("Invoke result does not dominate all uses!", Op,&I);
                return;
              }
        }
      } else if (isa<PHINode>(I)) {
        // PHI nodes are more difficult than other nodes because they actually
        // "use" the value in the predecessor basic blocks they correspond to.
        BasicBlock *PredBB = cast<BasicBlock>(I.getOperand(i+1));
        Assert2(DT->dominates(OpBlock, PredBB) ||
                !DT->isReachableFromEntry(PredBB),
                "Instruction does not dominate all uses!", Op, &I);
      } else {
        if (OpBlock == BB) {
          // If they are in the same basic block, make sure that the definition
          // comes before the use.
          Assert2(InstsInThisBlock.count(Op) || !DT->isReachableFromEntry(BB),
                  "Instruction does not dominate all uses!", Op, &I);
        }

        // Definition must dominate use unless use is unreachable!
        Assert2(InstsInThisBlock.count(Op) || DT->dominates(Op, &I) ||
                !DT->isReachableFromEntry(BB),
                "Instruction does not dominate all uses!", Op, &I);
      }
    } else if (isa<InlineAsm>(I.getOperand(i))) {
      Assert1(i == 0 && (isa<CallInst>(I) || isa<InvokeInst>(I)),
              "Cannot take the address of an inline asm!", &I);
    }
  }
  InstsInThisBlock.insert(&I);
}
*)

(* defns Jwf_insn_base *)
Inductive wf_insn_base : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> Prop :=    (* defn wf_insn_base *)
 | wf_insn_base_intro : forall (insn_id_l_list:list (insn*id*l)) (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_insn) (usedef_block5:usedef_block) (fdef5:fdef) (dt5:dt) (block5:block) (insn_5:insn) (list_insn5:list_insn) (insn':insn) (typ5 typ':typ) (ids5:ids) (module_info5:module_info) (fdef_info5:fdef_info) (ls5:ls),
     insnInSystemModuleFdefBlock insn_5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 ->
      (getInsnUseDef  usedef_insn5   insn_5  =  list_insn5 )  ->
      list_insn5  =  (map (fun (pat_:(insn*id*l)) => match pat_ with (insn_,id_,l_) => insn_ end ) insn_id_l_list)  ->
       ( isPhiNode insn_5 )   ->  (forall insn_, In (insn_) (map (fun (pat_:insn*id*l) => match pat_ with (insn_,id_,l_) => (insn_) end) insn_id_l_list) ->   ( isPhiNode insn_ )   ->   (   (  (not (  getInsnID  insn_5  = getInsnID  insn_  ))  )   \/   (  (isReachableFromEntry    ( fdef5 ,  dt5 )     block5 )  )   )  )  ->
       (  isTerminatorInsn insn_5  /\   (getTerminator  block5  =   (Some  insn' )  )   )   ->   (  getInsnID  insn_5  = getInsnID  insn'  )   ->
     getInsnTyp insn_5  (Some  typ5 )  ->
      typeEq typ5 typ_void  \/  isFirstClassTyp typ5  ->
        (  (not ( typeEq typ5 typ_metadata ))  )   \/  isInvokeInsn insn_5   \/  isCallInsn insn_5  ->
       ( isPointerTyp typ5 )   ->   (  getPointerEltTyp typ5 typ'  /\   (  (not ( typeEq typ' typ_metadata ))  )   )   ->
     getInsnOperands insn_5 ids5 ->
      ids5  =  (map (fun (pat_:(insn*id*l)) => match pat_ with (insn_,id_,l_) => id_ end ) insn_id_l_list)  ->
     (forall id_, In (id_) (map (fun (pat_:insn*id*l) => match pat_ with (insn_,id_,l_) => (id_) end) insn_id_l_list) -> (wf_operand intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn_5 id_)) ->
     getInsnLabels insn_5 ls5 ->
      ls5  =  (map (fun (pat_:(insn*id*l)) => match pat_ with (insn_,id_,l_) => l_ end ) insn_id_l_list)  ->
     (forall l_, In (l_) (map (fun (pat_:insn*id*l) => match pat_ with (insn_,id_,l_) => (l_) end) insn_id_l_list) -> (wf_label intrinsic_funs5 system5 module_info5 fdef_info5 block5 insn_5 l_)) ->
     wf_insn_base intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     ( fdef5 ,  dt5 )   block5 insn_5.

(* defns Jwf_insn *)
Inductive wf_insn : intrinsic_funs -> system -> module_info -> fdef_info -> block -> insn -> Prop :=    (* defn wf_insn *)
 | wf_insn_return : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block) (typ5:typ) (value5:value),
     wf_insn_base intrinsic_funs5 system5 module_info5   ( fdef5 ,  dt5 )   block5 (insn_return typ5 value5) ->
     getReturnTyp fdef5 typ5 ->
      (not ( typeEq typ5 typ_void ))  ->
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
     blockInSystemModuleFdef  (block_with_label l5 list_insn5)  system5 module_info5 fdef_info5 ->
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

