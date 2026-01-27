open Arg

(* Generate the worst cases in Fig1. of Finding Dominators in Practice 
   ocamlbuild gen.native
   ./gen.native -kit 50 -ksnca 1000 -kbfs 2000 -kdfs 2000
   These inputs generate large enough code, but not too large
*)

let switch (lname:String.t) (names:String.t list) : String.t =
match names with
  | [] -> failwith "switch needs at least one arg"
  | dname::names' -> 
     Printf.sprintf "%s: switch i32 0, label %%%s [ %s ]\n" 
       lname
       dname
       (snd 
         (List.fold_left 
          (fun (cnt, acc) name ->
           (cnt + 1,
           (Printf.sprintf "i32 %d, label %%%s " cnt name) ^ acc))
          (0, "") names'))

let br (lname:String.t) (name:String.t) =
Printf.sprintf "%s: br label %%%s\n" lname name

let br_cond (lname:String.t) (namet:String.t) (namef:String.t) =
Printf.sprintf "%s: br i1 0, label %%%s, label %%%s\n" lname namet namef

let lexit () =
"exit: ret void\n"

let rec sequence (out:out_channel) (names: String.t list) =
match names with
  | x::((y::_) as names') -> 
      output_string out (br x y); 
      sequence out names'
  | _ -> ()

let rec gen_names (prefix:String.t) (acc:String.t list) (num:int) =
if num <= 0 then acc
else gen_names prefix ((Printf.sprintf "%s%d" prefix num)::acc) (num-1)

let ksnca = ref 5
let kbfs = ref 5
let kdfs = ref 5
let kit = ref 5

let argspec = [
  ("-ksnca", Set_int ksnca, "snca");
  ("-kbfs", Set_int kbfs, "bfs");
  ("-kdfs", Set_int kdfs, "dfs");
  ("-kit", Set_int kit, "it");
]

let sncaworst fname k =
  let output = open_out fname in
  let xs = gen_names "x" [] k in
  let ys = gen_names "y" [] k in
  output_string output "define void @foo() {\n";
  output_string output (switch "entry" ((List.nth xs 0)::ys));
  sequence output xs;
  output_string output (switch (List.nth xs (k-1)) ys);
  List.iter (fun y -> output_string output (br y "exit")) ys;
  output_string output (lexit ());
  output_string output "}\n";
  close_out output

let ibfsquad fname k =
  let output = open_out fname in
  let xs = gen_names "x" [] k in
  output_string output "define void @foo() {\n";
  output_string output (br_cond "entry" "w" "y1");
  sequence output ("y1"::"y2"::List.nth xs (k-1)::[]);
  output_string output (switch "w" xs);
  sequence output (List.rev xs);
  output_string output (br (List.nth xs 0) "exit");
  output_string output (lexit ());
  output_string output "}\n";
  close_out output

let idfsquad fname k =
  let output = open_out fname in
  let ys = gen_names "y" [] k in
  let xs = gen_names "x" [] k in
  let zs = gen_names "z" [] k in
  let rec loop idx =
    if idx < k-1 then
      (output_string output 
         (br_cond (List.nth ys idx) (List.nth ys (idx+1)) (List.nth xs idx));
       output_string output 
         (br_cond (List.nth xs idx) (List.nth zs (idx+1)) (List.nth zs idx));
       output_string output (br (List.nth zs idx) (List.nth xs idx));
       loop (idx+1))
    else
      (output_string output (br_cond (List.nth ys idx) "exit" (List.nth xs idx));
       output_string output (br (List.nth xs idx) (List.nth zs idx));
       output_string output (br (List.nth zs idx) (List.nth xs idx)))
  in
  output_string output "define void @foo() {\n";
  output_string output (br_cond "entry" (List.nth ys 0) (List.nth zs 0));
  loop 0;  
  output_string output (lexit ());
  output_string output "}\n";
  close_out output

let itworst fname k =
  let output = open_out fname in
  let xs = gen_names "x" [] k in
  let ys = gen_names "y" [] k in
  let zs = gen_names "z" [] k in
  let ws = gen_names "w" [] k in
  let rec loopy idx =
    if idx < k-1 then
       (output_string output 
         (switch (List.nth ys idx) (List.nth ys (idx+1)::ws));
       loopy (idx+1))
    else
       output_string output 
         (switch (List.nth ys idx) (List.nth zs 0::ws))
  in
  let rec loopz idx =
    if idx < k-1 then
      ((if idx = 0 then
         output_string output 
           (br (List.nth zs idx) (List.nth zs (idx+1)))
       else
         output_string output 
           (br_cond (List.nth zs idx) 
                    (List.nth zs (idx-1)) (List.nth zs (idx+1))));
      loopz (idx+1))
    else
      if idx <> 0 then
        output_string output 
         (br (List.nth zs idx) (List.nth zs (idx-1)));
  in
  output_string output "define void @foo() {\n";
  output_string output 
    (switch "entry" 
      ((List.nth ws 0)::(List.nth xs 0)::(List.nth zs (k-1))::[]));
  sequence output xs;
  sequence output ws;
  output_string output (br (List.nth xs (k-1)) (List.nth ys 0));
  output_string output (br (List.nth ws (k-1)) "exit");
  loopy 0;
  loopz 0;
  output_string output (lexit ());
  output_string output "}\n";
  close_out output

let () =
  Arg.parse argspec (fun _ -> ()) "gen \n";
  sncaworst "sncaworst_large.ll" !ksnca;
  ibfsquad "ibfsquad_large.ll" !kbfs;
  idfsquad "idfsquad_large.ll" !kdfs;
  itworst "itworst_large.ll" !kit
