open Printf
open Llvm
open Symexe
open Pretty_printer

let main in_filename out_filename =
	let c = create_context () in
	let mbuf = MemoryBuffer.of_file in_filename in
	let m = Llvm_bitreader.parse_bitcode c mbuf in
	let st = SlotTracker.create_of_module m in
	
	(* I use prerr but not print, because dump_ outputs to stderr. *)
	dump_module m;
	
	prerr_endline "Travel me:";
	travel_module st m;
	
	(* write the module to a file *)
	if not (Llvm_bitwriter.write_bitcode_file m out_filename) then exit 1;
	SlotTracker.dispose st;
	dispose_module m

let () = match Sys.argv with
	| [| _; in_filename; out_filename |] -> main in_filename out_filename
	| _ -> main "Input.bc" "Output.bc"
