open Interpreter
open Printf
open Llvm
open Arg

let nullpass = ref false
let mem2reg = ref true
let mem2reg_opt = ref 0
let does_remove_lifetime = ref false
let does_remove_dbg = ref false
let out_file = ref stdout
let net_time = ref false

let main in_filename =
  let parse_time = ref 0.0 in
  let work_time = ref 0.0 in
  let print_time = ref 0.0 in
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
  parse_time := Sys.time ();
  (* Print [coqim] *)
  (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim);

  (if !nullpass then 
    (* Translate [coqim] to a *.ll file *)
    Coq2ll.travel_module !out_file coqim
  else
    (* M2R [coqim], output [coqom]  *)
    let coqim0 =
      if !does_remove_lifetime then 
        Primitives.remove_lifetime_from_module coqim 
      else coqim 
    in
    let coqim1 =
      if !does_remove_dbg then 
        Primitives.remove_dbg_declares_from_module coqim0
      else coqim0 
    in
    let vm2r = (match !mem2reg_opt with
      | 2 -> Vmem2reg_opt2.run 
      | 1 -> Vmem2reg_opt.run 
      | _ -> Vmem2reg.run) in
    let coqom = Primitives.fix_temporary_module (vm2r coqim1) in
    work_time := Sys.time () -. !parse_time;
    (* Print [coqom] *)
    (if !Globalstates.debug then Coq_pretty_printer.travel_module coqom);
    (* Translate [coqom] to a *.ll file *)
    Coq2ll.travel_module !out_file coqom;
    print_time := Sys.time () -. !work_time;
    (if !net_time then 
       printf "parse:%f work:%f print:%f\n" !parse_time !work_time !print_time)
  );

  SlotTracker.dispose ist;
  dispose_module im

let argspec = [
  ("-net-time", Set net_time, "print time of parse/work/print");
  ("-null", Set nullpass, "null pass");
  ("-d", Set Globalstates.debug, "debug");
  ("-mem2reg", Set mem2reg, "mem2reg (pipelined by default)");
  ("-opt", Unit (fun () -> mem2reg_opt:=1), "optimized mem2reg");
  ("-O", Set_int mem2reg_opt, "optimized mem2reg");
(*  ("-composed", Clear Globalstates.does_macro_m2r, "composed mem2reg"); *)
  ("-prune", Set Globalstates.does_dead_phi_elim, "pruned");
  ("-remove-lifetime", Set does_remove_lifetime, "remove lifetime intrinsics");
  ("-remove-dbg", Set does_remove_dbg, "remove debug intrinsics");
  ("-no-stld-elim", Clear Globalstates.does_stld_elim, "do not remove st/ld pairs");
  ("-maximal", Clear Globalstates.does_phi_elim, "maximal");
  ("-o", String (fun s -> 
                 try 
                   out_file := open_out s
                 with
     	           | Sys_error _ -> failwith ("cannot open " ^ s)), 
         "output file")
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
