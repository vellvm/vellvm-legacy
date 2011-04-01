open Printf
open Llvm

let debug = false

let main in_filename out_filename =
	let ic = create_context () in
	let imbuf = MemoryBuffer.of_file in_filename in
	let im = Llvm_bitreader.parse_bitcode ic imbuf in
	let ist = SlotTracker.create_of_module im in
	
	(* dump_module im; *)
	(* Llvm_pretty_printer.travel_module ist im; *)
	let coqim = Llvm2coq.translate_module debug ist im in
	(* Coq_pretty_printer.travel_module coqim; *)

	let oc = create_context () in
	let ombuf = MemoryBuffer.of_file out_filename in
	let om = Llvm_bitreader.parse_bitcode oc ombuf in
	let ost = SlotTracker.create_of_module om in

	let coqom = Llvm2coq.translate_module debug ost om in
			
	(* eprintf "EqTV=%b\n" (Eq_tv.tv_module coqim coqom); *)
	eprintf "SubTV=%b MTV=%b\n" (Sub_tv.tv_module coqim coqom) 
          (Sub_tv.mtv_module coqom);
	
	(* Coq2llvm.translate_module coqom; *)
	
	(* write the module to a file *)
	(* if not (Llvm_bitwriter.write_bitcode_file m out_filename) then exit 1; *)
	
	SlotTracker.dispose ist;
	SlotTracker.dispose ost;
	dispose_module im;
	dispose_module om

let () = match Sys.argv with
	| [| _; in_filename; out_filename |] -> main in_filename out_filename
	| _ -> main "Input.bc" "Output.bc"

