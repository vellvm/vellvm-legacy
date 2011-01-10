open Assert


(* These tests are provided by you -- they will graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
Test ("Test1", 
[
	("case1", assert_eqf (fun () -> 3) 5);
	("case2", assert_fail);
	("case3", fun () -> raise Not_found);
]);

Test ("Test4",
[
	("case1", assert_eq 3 3);
	("case2", fun () -> ());
]);
				
] 
