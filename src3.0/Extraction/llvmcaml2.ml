open Llvm_executionengine
open Syntax
open LLVMsyntax
open Printf
open Llvm
open Llvm_aux
open Llvmcaml

  let callExternalFunction (td:TargetData.t) 
                           (gl:(LLVMsyntax.id * Llvmcaml.GenericValue.t) list) 
                           m (fid:LLVMsyntax.id) 
                           (tret: LLVMsyntax.typ) (targs: LLVMsyntax.typ list)
                           (dck:LLVMsyntax.deckind) (args:GenericValue.t list) = 
    (if !Globalstates.debug then 
      eprintf "  Mcall external fun=%s\n" fid;flush_all());
    let (ee, mm) = m in
    match Llvm.lookup_function (getRealName fid) mm with
    | Some fv -> 
	Some ((Some 
                (ExecutionEngine.call_external_function fv 
                  (Array.of_list args) ee), 
               Events.coq_E0), 
              m)
    | None -> failwith "callExternalFunction: cannot find function"

