open Ssa_interpreter
open Sb_db_trans
open Sb_ds_trans
open Printf
open Llvm
open Trace

let main in_filename =
  let ic = global_context () in
  let imbuf = MemoryBuffer.of_file in_filename in
  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let ist = SlotTracker.create_of_module im in

  (if !Globalstates.debug then dump_module im);
  (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist im);
  let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in
  (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim);

  (match SB_ds_pass.trans_module coqim with
  | Some coqom -> 
      (if !Globalstates.debug then Coq_pretty_printer.travel_module coqom);
      Coq2ll.travel_module coqom
  | None -> failwith "failed");

  SlotTracker.dispose ist;
  dispose_module im

let () = match Sys.argv with
  | [| _; "-d" ; in_filename |] -> 
       Globalstates.debug := true; main in_filename
  | [| _; in_filename |] -> main in_filename
  | _ -> main "input.bc"
