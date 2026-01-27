open Printf
open BinPos
open Syntax
open ListSet
open MetatheoryAtom
open Maps
open Kildall
open Dfs

let rec dfs_aux (succs: LLVMsyntax.ls ATree.t)
  (acc: positive*unit ATree.t*positive ATree.t*LLVMsyntax.l PTree.t) 
  (todo: LLVMsyntax.ls): 
  positive*unit ATree.t*positive ATree.t*LLVMsyntax.l PTree.t =
  match todo with
  | [] -> acc
  | next::todo' ->
      let (po, visited, a2p, p2a) = acc in
      match ATree.get next visited with
      | None -> 
          let (po', visited', a2p', p2a') = 
            dfs_aux succs (po, ATree.set next () visited, a2p, p2a)
              (XATree.successors_list succs next) in
          dfs_aux succs (coq_Psucc po', visited', 
                         ATree.set next po' a2p', 
                         PTree.set po' next p2a') todo'
      | Some _ -> dfs_aux succs acc todo'

let dfs (succs: LLVMsyntax.ls ATree.t) (le:LLVMsyntax.l) (po: positive):
    positive ATree.t*LLVMsyntax.l PTree.t =
  let (po', visited, a2p, p2a) = 
    dfs_aux succs (po, ATree.empty, ATree.empty, PTree.empty)
      (XATree.successors_list succs le) in
  (ATree.set le po' a2p, PTree.set po' le p2a)

let rec bfs_aux (succs: LLVMsyntax.ls ATree.t)
  (acc: positive*unit ATree.t*positive ATree.t) (todo: LLVMsyntax.ls): 
  positive*unit ATree.t*positive ATree.t =
  match todo with
  | [] -> acc
  | next::todo' ->
      let (po, visited, a2p) = acc in
      match ATree.get next visited with
      | Some _ -> bfs_aux succs acc todo'
      | None ->
          bfs_aux succs 
            (coq_Psucc po, ATree.set next () visited, ATree.set next po a2p)
            (todo' @ XATree.successors_list succs next)

let bfs (succs: LLVMsyntax.ls ATree.t) (le:LLVMsyntax.l) (po: positive):
    positive ATree.t = 
  let (_, _, a2p) = 
    bfs_aux succs (po, ATree.empty, ATree.empty) (le::[]) in
  a2p

