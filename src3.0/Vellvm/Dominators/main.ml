open Printf
open Llvm
open Syntax
open Infrastructure
open Camlcoq
open Maps
open Transforms_aux
open Arg

let dom_type = ref 0
let gen_dtree = ref true
let only_pdtree = ref false

let slow_dom f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
       let b0 = Cfg.bound_fdef f in
       let dts = Dom_set.AlgDom.dom_query f in
       ignore(print_dominators b0 dts);
       if !gen_dtree then
           (match Analysis.reachablity_analysis f with
            | Some rd ->
               let LLVMsyntax.Coq_block_intro (root, _, _, _) = b in
               let chains = Dom_set_tree.compute_sdom_chains dts rd in
               let dt = Dom_tree.create_dtree_from_chains 
                          MetatheoryAtom.AtomImpl.eq_atom_dec root chains in
               ignore (print_dtree (fun a->a) dt)
           | None -> ())
     | None -> ()

let print_doms (dms: Push_iter.LDoms.t PMap.t) =
  let (_, cnts) = dms in
  PTree.map (fun key ods ->
             eprintf "%ld <<" (camlint_of_positive key);
             (match ods with
               | None -> ()
               | Some ds ->
                   List.iter (fun d -> eprintf "%ld " (camlint_of_positive d)) ds
             );
             eprintf "\n") cnts

let pull_dom f =
  let dts = Pull_iter.dom_analyze f in
  if (!Globalstates.print_dtree) then (ignore (print_doms dts))

let push_dom f =
  let (dts, a2p) = Dom_list.dom_analyze f in 
  if (!Globalstates.print_dtree) then (ignore (print_doms dts))

let push_adtree f =
  match Dom_list.AlgDom'.create_dom_tree f with
  | Some dt -> if (!Globalstates.print_dtree) 
               then ignore (print_dtree (fun a -> a) dt)
  | None -> ()

let push_pdtree f =
  let (dts, a2p) = Dom_list.dom_analyze f in 
  if (!Globalstates.print_dtree) then (ignore (print_doms dts));
  match LLVMinfra.getEntryLabel f with
  | Some le ->
     (match ATree.get le a2p with
      | Some pe -> 
          let res = fun p -> PMap.get p dts in
          let pdt = Dom_list_tree.create_dtree pe 
                      (Dom_list.get_reachable_nodes (Cfg.bound_fdef f) a2p) 
                      res in
          if (!Globalstates.print_dtree) 
          then ignore (print_dtree 
                         (fun a -> sprintf "%ld" (camlint_of_positive a)) pdt)
      | None -> ())
  | None -> ()

let dom_product g =
  match g with
  | LLVMsyntax.Coq_product_fdef 
      (LLVMsyntax.Coq_fdef_intro 
        (LLVMsyntax.Coq_fheader_intro (_, _, fid, _, _), _) as f) -> 
      (if (!Globalstates.print_dtree) then eprintf "Dom %s:\n" fid);
      (match !dom_type with
	| 0 -> if !gen_dtree then 
                 (if !only_pdtree then push_pdtree f else push_adtree f)
               else push_dom f 
	| 1 -> pull_dom f 
	| 2 -> slow_dom f      
	| _ -> ())
  | _ -> ()

let dom_module m =
  match m with
  | LLVMsyntax.Coq_module_intro (_, _, ps) -> 
    List.iter dom_product ps

let main in_filename =
  (* Read bitcode [in_filename] into LLVM module [im] *)
  let ic = global_context () in
  let imbuf = MemoryBuffer.of_file in_filename in
  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let ist = SlotTracker.create_of_module im in

  (* Translate LLVM module [im] to Coq module [coqim] *)
  let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in

  dom_module coqim;

  SlotTracker.dispose ist;
  dispose_module im

let argspec = [
  ("-d", Set Globalstates.print_dtree, "debug. Default=false");
  ("-type", Set_int dom_type, "0:push; 1:pull; 2:slow; others:llvm. Default=0");
  ("-notree", Clear gen_dtree, "Do not generate dom-tree explicitly. Default=true");
  ("-only-pdtree", Set only_pdtree, "Only generate positive dtree. Default=false");
]

let worklist = ref []

let () = 
  Arg.parse argspec (fun f -> worklist := f :: !worklist) "dom-analysis \n";
  match !worklist with
  | [] -> main "input.bc"
  | filename::_ -> main filename

(* let () =  *)
(*   match Sys.argv with *)
(*   | [| _; in_filename |] ->  *)
(*        main in_filename *)
(*   | [| _; "-pull-dom"; in_filename |] ->  *)
(*        dom_type := 1; *)
(*        main in_filename *)
(*   | [| _; "-slow-dom"; in_filename |] ->  *)
(*        dom_type := 2; *)
(*        main in_filename *)
(*   | [| _; "-llvm-dom"; in_filename |] ->  *)
(*        dom_type := 3; *)
(*        Globalstates.gen_llvm_dtree := true; *)
(*        main in_filename *)
(*   | [| _; "-dpush-dom" ; in_filename |] ->  *)
(*        Globalstates.print_dtree := true;  *)
(*        main in_filename *)
(*   | [| _; "-dpull-dom" ; in_filename |] ->  *)
(*        dom_type := 1; *)
(*        Globalstates.print_dtree := true;  *)
(*        main in_filename *)
(*   | [| _; "-dslow-dom"; in_filename |] ->  *)
(*        dom_type := 2; *)
(*        Globalstates.print_dtree := true;  *)
(*        main in_filename *)
(*   | [| _; "-dllvm-dom"; in_filename |] ->  *)
(*        dom_type := 3; *)
(*        Globalstates.print_dtree := true;  *)
(*        Globalstates.gen_llvm_dtree := true; *)
(*        main in_filename *)
(*   | _ -> main "input.bc" *)
