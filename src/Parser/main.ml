open Printf
open Llvm
open Symexe

let main in_filename out_filename =
	let c = create_context () in
	let mbuf = MemoryBuffer.of_file in_filename in
	let m = Llvm_bitreader.parse_bitcode c mbuf in
	let st = SlotTracker.create_of_module m in
	
	(* I use prerr but not print, because dump_ outputs to stderr. *)
	dump_module m;
	
	Llvm_pretty_printer.travel_module st m;
	
	let coqm = Translator.translate_module st m in 	
	Coq_pretty_printer.travel_module coqm;	
	eprintf "TV=%b\n" (tv_module coqm coqm);
	
	(* write the module to a file *)
	if not (Llvm_bitwriter.write_bitcode_file m out_filename) then exit 1;
	SlotTracker.dispose st;
	dispose_module m

let () = match Sys.argv with
	| [| _; in_filename; out_filename |] -> main in_filename out_filename
	| _ -> main "Input.bc" "Output.bc"
