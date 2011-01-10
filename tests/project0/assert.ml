(* CIS341 Assertion Testing and Grading Infrastructure *)
(* Author: Steve Zdancewic                             *)

(* Do NOT modify this file -- we will overwrite it     *)
(* with our own version when testing your code.        *)



(* An assertion is just a unit->unit function that either *)
(* succeeds silently or throws an Failure exception.       *)
type assertion = (unit -> unit)

type 'a test = 
	| GradedTest of string * int * (string * 'a) list
	| Test of string * (string * 'a) list

type suite = (assertion test) list


(**************)
(* Assertions *)

let assert_eq v1 v2 : assertion =
	fun () -> if v1 <> v2 then failwith "not equal" else ()

let assert_eqf f v2 : assertion =
	fun () -> if (f ()) <> v2 then failwith "not equal" else ()

let assert_fail : assertion = fun () -> failwith "assert fail"



(***************************)
(* Generating Test Results *)

type result = 
	| Pass 
	| Fail of string

type outcome = (result test) list

let run_assertion (f:assertion) : result =
	try 
		f ();
		Pass
  with
		| Failure m -> Fail m
	  | _ -> Fail "test threw an unknown exception"

let run_test (t:assertion test) : result test =
	let run_case (cn, f) = (cn, run_assertion f) in
	begin match t with
		| GradedTest (n,s,cases) -> GradedTest(n,s,List.map run_case cases)
		| Test (n, cases) -> Test(n, List.map run_case cases)
	end
	
let run_suite (s:suite):outcome =
	List.map run_test s





(***********************)
(* Reporting functions *)

let result_test_to_string (name_pts:string) (r:result test): string =
	let string_of_case (name, res) = 
		"  " ^ name ^ ": " ^ (
		begin match res with
			| Pass     -> "passed"
			| Fail msg -> "failed - " ^ msg
		end
		) in
	begin match r with
		| GradedTest (_, _, cases) ->
			name_pts ^
			(List.fold_left (fun rest -> fun case -> rest ^ "\n" ^ (string_of_case case)) "" cases)
		| Test (_, cases) ->
			name_pts ^ ":" ^ 
			(List.fold_left (fun rest -> fun case -> rest ^ "\n" ^ (string_of_case case)) "" cases)
	end

(* returns (name_pts, passed, failed, total, points_earned, max_given, max_hidden) *)
let get_results (t:result test) =
	let num_passed cases = 
		List.fold_left (fun cnt (_,r) -> match r with Pass -> cnt + 1 | _ -> cnt) 0 cases in
	let num_failed cases = 
		List.fold_left (fun cnt (_,r) -> match r with Fail _ -> cnt + 1 | _ -> cnt) 0 cases in
	begin match t with
		| GradedTest (name,pts,cases) ->
			let passed = num_passed cases in
			let failed = num_failed cases in
			let total = List.length cases in
			if total > 0 then
					let points_earned = ((float_of_int passed) /. (float_of_int total)) *. (float_of_int pts) in
					let name_pts = Printf.sprintf "%s (%1.f/%d points)" name points_earned pts in
					(name_pts, passed, failed, total, points_earned, pts, 0)
				else
					let name_pts = Printf.sprintf "%s (??/%d points)" name pts in
					(name_pts, passed, failed, total, 0.0, 0, pts)
		| Test(name, cases) ->
			let total = List.length cases in
			let passed = num_passed cases in
			let failed = num_failed cases in
			(name, passed, failed, total, 0.0, 0, 0)
	end

let outcome_to_string (o:outcome):string =
	let sep = "\n---------------------------------------------------\n" in
	let helper  (passed, failed, total, pts, maxg, maxh, str) (t:result test) =
		let (name_pts, p, f, tot, s, mg, mh) = get_results t in
		(passed + p, failed + f, total + tot, s +. pts, maxg + mg, maxh + mh, 
		str ^ "\n" ^ (
			if f > 0 then (result_test_to_string name_pts t) else 
		  if tot > 0 then (name_pts ^ ":\n  OK") else
				(name_pts ^ ":\n  Hidden") 
			)
		) in
	let (p,f,tot,pts,maxg, maxh,str) = List.fold_left helper (0,0,0,0.0,0,0,"") o in
	str ^ sep ^ (Printf.sprintf "Passed: %d/%d\nFailed: %d/%d\nScore: %1.f/%d (given)\n       ??/%d (hidden)" p tot f tot pts maxg maxh)
	



