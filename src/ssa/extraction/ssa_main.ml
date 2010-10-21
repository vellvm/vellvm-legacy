open Ssa_interpreter
open Ssa_dynamic
open Printf
open Llvm
open Llvm_executionengine
open Trace

let rec interInsnStar (s:LLVMopsem.coq_State) (tr:trace) (n:int) : (LLVMopsem.coq_State*trace) option =
	if (LLVMopsem.ds_isFinialState s) 
	then Some (s, tr)
	else
		if n > 0 
		then
	    begin
			eprintf "n=%d\n" n; 
			flush_all();		
			match interInsn s with
      | Some (s', tr') -> interInsnStar s' (trace_app tr tr') (n-1)  
      | None -> None
			end
		else Some (s, tr)
			
let main in_filename  =

        let ic = global_context () in
        let imbuf = MemoryBuffer.of_file in_filename in
        let im = Llvm_bitreader.parse_bitcode ic imbuf in
        let ist = SlotTracker.create_of_module im in
        let imp = ModuleProvider.create im in

        dump_module im;
        Llvm_pretty_printer.travel_module ist im;
        let coqim = Llvm2coq.translate_module ist im in
        Coq_pretty_printer.travel_module coqim;

        let li = ExecutionEngine.create_interpreter imp in

        (match LLVMopsem.ds_genInitState (coqim::[]) "@main" [] (li, im) with
          | Some s -> 
            (match interInsnStar s Coq_trace_nil 100 with
              | Some (s', tr) -> ()
              | None -> () )
          | None -> () );

        SlotTracker.dispose ist;
        ExecutionEngine.dispose li;
        ModuleProvider.dispose imp

let () = match Sys.argv with
        | [| _; in_filename |] -> main in_filename
        | _ -> main "Input.bc"




