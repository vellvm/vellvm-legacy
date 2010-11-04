open Ssa_interpreter
open Ssa_dynamic
open Printf
open Llvm
open Llvm_executionengine
open Trace

let interInsnLoop (s0:LLVMopsem.coq_State) (tr0:trace) : (LLVMopsem.coq_State*trace) option =
	
	let s = ref s0 in
	let n = ref 0 in
	
	while not (LLVMopsem.ds_isFinialState !s) do
  	(if !Globalstates.debug then (eprintf "n=%d\n" !n;	 flush_all()));		
		match interInsn !s with
    | Some (s', _) ->
			begin 
			  s := s';
			  n := !n + 1
			end 
    | None -> failwith "Stuck!" 
	done;
	
	Some (!s, Coq_trace_nil)
	
let rec interInsnStar (s:LLVMopsem.coq_State) (tr:trace) (n:int) : (LLVMopsem.coq_State*trace) option =
	if (LLVMopsem.ds_isFinialState s) 
	then 
		begin
			(if !Globalstates.debug then (eprintf "Done!\n";flush_all()));
			Some (s, tr)
    end			
	else
		if n > 0 
		then
	    begin
			(if !Globalstates.debug then (eprintf "n=%d\n" n;	 flush_all()));		
			match interInsn s with
      | Some (s', tr') -> interInsnStar s' (trace_app tr tr') (n-1)  
      | None ->
				eprintf "Stuck!\n";flush_all(); 
				None
			end
		else 
			begin
				eprintf "Time up!\n";flush_all();
				Some (s, tr)
      end				
			
let main in_filename  =

        let ic = global_context () in
        let imbuf = MemoryBuffer.of_file in_filename in
        let im = Llvm_bitreader.parse_bitcode ic imbuf in
        let ist = SlotTracker.create_of_module im in
        let imp = ModuleProvider.create im in

        (if !Globalstates.debug then dump_module im);
        (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist im);
        let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in
        (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim);

        let li = ExecutionEngine.create_interpreter imp in

        (match LLVMopsem.ds_genInitState (coqim::[]) "@main" [] (li, im) with
          | Some s -> 
            (match interInsnLoop s Coq_trace_nil with
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
							Globalstates.debug := true
						)
					);
        	main (Array.get Sys.argv 1)
				)
