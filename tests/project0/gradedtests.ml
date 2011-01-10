open Assert


(* Test suite for hellocaml.ml *)

(* Do NOT modify this file -- we will overwrite it with our *)
(* own version when we test your homework.                  *)


(* These tests will be used to grade your assignment *)
let graded_tests : suite = [	
GradedTest ("Test2", 10,
[
	("case1", assert_eq 3 5);
	("case2", assert_eq "test1.oat" "test2.oat");
	("case3", assert_eq 4 4);
]);

GradedTest ("Test3", 20, 
[]);


GradedTest ("Test5", 10,
[
	("case1", assert_eq 3 3);
	("case2", assert_eq 4 4);
]);

]
