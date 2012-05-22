open Interpreter
open Printf
open Llvm
open Arg

let nullpass = ref false
let mem2reg = ref true
let does_remove_lifetime = ref false

let main in_filename =
  (* Read bitcode [in_filename] into LLVM module [im] *)
  let ic = global_context () in
  let imbuf = MemoryBuffer.of_file in_filename in
  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let ist = SlotTracker.create_of_module im in

  (* Print [im] by LLVM pinter *)
  (if !Globalstates.debug then dump_module im);
  (* Print [im] by My pinter *)
  (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist im);
  (* Translate LLVM module [im] to Coq module [coqim] *)
  let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in
  (* Print [coqim] *)
  (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim);

  (if !nullpass then 
    (* Translate [coqim] to a *.ll file *)
    Coq2ll.travel_module coqim
  else
    (if !mem2reg then 
      (* GVN [coqim], output [coqom]  *)
      let coqim' = 
        if !does_remove_lifetime then 
          Transforms_aux.remove_lifetime_from_module coqim 
        else coqim
      in
      let coqom = Mem2reg.run coqim' in
      (* Print [coqom] *)
      (if !Globalstates.debug then Coq_pretty_printer.travel_module coqom);
      (* Translate [coqom] to a *.ll file *)
      Coq2ll.travel_module coqom

    else
      (* GVN [coqim], output [coqom]  *)
      let coqom = Gvn.opt coqim in
      (* Print [coqom] *)
      (if !Globalstates.debug then Coq_pretty_printer.travel_module coqom);
      (* Translate [coqom] to a *.ll file *)
      Coq2ll.travel_module coqom);
  );

  SlotTracker.dispose ist;
  dispose_module im

let argspec = [
  ("-null", Set nullpass, "null pass");
  ("-d", Set Globalstates.debug, "debug");
  ("-mem2reg", Set mem2reg, "mem2reg (pipelined by default)");
  ("-composed", Clear Globalstates.does_macro_m2r, "composed mem2reg");
  ("-prune", Set Globalstates.does_dead_phi_elim, "pruned");
  ("-remove-lifetime", Set does_remove_lifetime, "remove lifetime intrinsics");
  ("-no-stld-elim", Clear Globalstates.does_stld_elim, "do not remove st/ld pairs");
  ("-maximal", Clear Globalstates.does_phi_elim, "maximal");
]

let worklist = ref []

let () = 
  Arg.parse argspec (fun f -> worklist := f :: !worklist) "Vmem2reg \n";
  match !worklist with
  | [] -> main "input.bc"
  | filename::_ -> main filename

(* let () = match Sys.argv with *)
(*   | [| _; "-null" ; in_filename |] ->  *)
(*        nullpass := true;  *)
(*        main in_filename *)
(*   | [| _; "-mem2reg-dead-phi-elim" ; in_filename |] ->  *)
(*        mem2reg := true;  *)
(*        Globalstates.does_dead_phi_elim := true;  *)
(*        main in_filename *)
(*   | [| _; "-mem2reg" ; in_filename |] ->  *)
(*        mem2reg := true;  *)
(*        main in_filename *)
(*   | [| _; "-mem2reg-no-stld-elim" ; in_filename |] ->  *)
(*        mem2reg := true;  *)
(*        Globalstates.does_stld_elim := false;  *)
(*        Globalstates.does_phi_elim := false;  *)
(*        main in_filename *)
(*   | [| _; "-mem2reg-no-phi-elim" ; in_filename |] ->  *)
(*        Globalstates.does_phi_elim := false;  *)
(*        mem2reg := true;  *)
(*        main in_filename *)
(*   | [| _; "-dmem2reg" ; in_filename |] ->  *)
(*        mem2reg := true;  *)
(*        Globalstates.debug := true;  *)
(*        main in_filename *)
(*   | [| _; "-Mem2reg" ; in_filename |] ->  *)
(*        Globalstates.does_macro_m2r := false ;  *)
(*        mem2reg := true;  *)
(*        main in_filename *)
(*   | [| _; "-Mem2reg-no-phi-elim" ; in_filename |] ->  *)
(*        Globalstates.does_macro_m2r := false ;  *)
(*        Globalstates.does_phi_elim := false;  *)
(*        mem2reg := true;  *)
(*        main in_filename *)
(*   | [| _; "-gvn" ; in_filename |] ->  *)
(*        mem2reg := false;  *)
(*        main in_filename *)
(*   | [| _; "-disable-pre" ; in_filename |] ->  *)
(*        Globalstates.does_pre := false;  *)
(*        main in_filename *)
(*   | [| _; "-disable-load-elim" ; in_filename |] ->  *)
(*        mem2reg := false;  *)
(*        Globalstates.does_load_elim := false;  *)
(*        main in_filename *)
(*   | [| _; "-disable-both" ; in_filename |] ->  *)
(*        mem2reg := false;  *)
(*        Globalstates.does_load_elim := false;  *)
(*        Globalstates.does_pre := false;  *)
(*        main in_filename *)
(*   | [| _; "-dgvn" ; in_filename |] ->  *)
(*        mem2reg := false;  *)
(*        Globalstates.debug := true;  *)
(*        main in_filename *)
(*   | [| _; in_filename |] ->  *)
(*        main in_filename *)
(*   | _ -> main "input.bc" *)
