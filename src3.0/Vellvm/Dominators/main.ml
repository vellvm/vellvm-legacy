open Printf
open Llvm
open Syntax
open Infrastructure
open Camlcoq
open Maps
open Transforms_aux
open Dtree

let dom_type = ref 0

let slow_dom f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (root, _, _, _) = b in
        (match Analysis.reachablity_analysis f with
          | Some rd ->
             let b0 = Analysis.bound_fdef f in
             let dts = Analysis.dom_analyze f in
             let chains = compute_sdom_chains b0 dts rd in
             let dt = List.fold_left 
                        (fun acc elt ->
                         let y,chain = elt in
                         create_dtree_from_chain acc chain) 
                        (DT_node (root, DT_nil)) chains in
             ignore(print_dominators b0 dts);
             ignore(print_dtree dt)
          | None -> ())
     | None -> ()

let print_doms (dms: Fast_iter.LDoms.t PMap.t) =
  let (_, cnts) = dms in
  PTree.map (fun key ods ->
             eprintf "%ld <<" (camlint_of_positive key);
             (match ods with
               | None -> ()
               | Some ds ->
                   List.iter (fun d -> eprintf "%ld " (camlint_of_positive d)) ds
             );
             eprintf "\n") cnts

let fast_dom f =
  let dts = Fast_iter.dom_analyze f in
  if (!Globalstates.print_dtree) then (ignore (print_doms dts))

let dom_product g =
  match g with
  | LLVMsyntax.Coq_product_fdef 
      (LLVMsyntax.Coq_fdef_intro 
        (LLVMsyntax.Coq_fheader_intro (_, _, fid, _, _), _) as f) -> 
      (if (!Globalstates.debug) then eprintf "Dom %s:\n" fid);
      (match !dom_type with
	| 0 -> fast_dom f 
	| 1 -> slow_dom f      
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

let () = 
  match Sys.argv with
  | [| _; in_filename |] -> 
       main in_filename
  | [| _; "-slow-dom"; in_filename |] -> 
       dom_type := 1;
       main in_filename
  | [| _; "-llvm-dom"; in_filename |] -> 
       dom_type := 2;
       Globalstates.gen_llvm_dtree := true;
       main in_filename
  | [| _; "-dfast-dom" ; in_filename |] -> 
       Globalstates.print_dtree := true; 
       main in_filename
  | [| _; "-dslow-dom"; in_filename |] -> 
       dom_type := 1;
       Globalstates.print_dtree := true; 
       main in_filename
  | [| _; "-dllvm-dom"; in_filename |] -> 
       dom_type := 2;
       Globalstates.print_dtree := true; 
       Globalstates.gen_llvm_dtree := true;
       main in_filename
  | _ -> main "input.bc"
