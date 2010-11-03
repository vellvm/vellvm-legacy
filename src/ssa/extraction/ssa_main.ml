open Ssa_interpreter
open Ssa_dynamic
open Printf
open Llvm
open Llvm_executionengine
open Trace

let debug = ref false

let rec interInsnStar (s:LLVMopsem.coq_State) (tr:trace) (n:int) : (LLVMopsem.coq_State*trace) option =
	if (LLVMopsem.ds_isFinialState s) 
	then 
		begin
			(if !debug then (eprintf "Done!\n";flush_all()));
			Some (s, tr)
    end			
	else
		if n > 0 
		then
	    begin
			(if !debug then (eprintf "n=%d\n" n;	 flush_all()));		
			match interInsn s with
      | Some (s', tr') -> interInsnStar s' (trace_app tr tr') (n-1)  
      | None ->
				(if !debug then (eprintf "Stuck!\n";flush_all())); 
				None
			end
		else 
			begin
				(if !debug then (eprintf "Time up!\n";flush_all()));
				Some (s, tr)
      end				
			
let main in_filename  =

        let ic = global_context () in
        let imbuf = MemoryBuffer.of_file in_filename in
        let im = Llvm_bitreader.parse_bitcode ic imbuf in
        let ist = SlotTracker.create_of_module im in
        let imp = ModuleProvider.create im in

        (if !debug then dump_module im);
        (if !debug then Llvm_pretty_printer.travel_module ist im);
        let coqim = Llvm2coq.translate_module !debug ist im in
        (if !debug then Coq_pretty_printer.travel_module coqim);

        let li = ExecutionEngine.create_interpreter imp in

        (match LLVMopsem.ds_genInitState (coqim::[]) "@main" [] (li, im) with
          | Some s -> 
            (match interInsnStar s Coq_trace_nil 1000 with
              | Some (s', tr) -> ()
              | None -> () )
          | None -> () );

        SlotTracker.dispose ist;
        ExecutionEngine.dispose li

let _ = if Array.length Sys.argv = 0 then
	        failwith "# of argv is 0"
				else if Array.length Sys.argv = 1 then
          main "Input.bc"
				else(   
					(if Array.length Sys.argv > 2 then
					  (if Array.get Sys.argv 2 = "-d" then 
							debug := true
						)
					);
        	main (Array.get Sys.argv 1)
				)
