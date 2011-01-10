(* hellocaml.ml *)
(* This is an individual project. *)

(* To use Eclipse with the OcaIDE plugin:
 * 
 *  1. Import the project0 directory into your eclipse workspace.
 *        File > Import  [General > File System]
 *        click [Next]
 *        Browse to the project0 directory.
 *        follow the prompts, selecting "OCamlBuild" as the OCaml project type.
 *  2. Configure the Project settings in Eclipse
 *        Project > Properties
 *         under Project > Targets   add   main.byte and main.native
 *  3. Compile the Project 
 *       via Project > Clean or Project > Build
 *       By default in Eclipse, the project will rebuild every time you save one of 
 *       its files.
 *  4. Run the project 
 *       Create a "Run Configuration" under Run > Run Configurations...
 *       Enter "project0" for the project name
 *       Browse to the _build/native.native for the executable.
 *       
 *       You can run it from the Run menu, or by right clicking on project0 in the
 *       navigator pane. 					   
 *) 

(* 
 * If using the command line:
 * First change to the project0 directory.
 *   > cd project0
 *
 * Then build the OUnit files:
 *
 *   > ocamlc -c oUnit.mli oUnit.ml
 *
 * You can experiment using the OCaml toplevel:
 *
 *   > ocaml
 *           Objective Caml version 3.12.0
 *   
 *   #
 *   > #load "unix.cma";;
 *   > #load "oUnit.cmo";;
 *   > #use "hellocaml.ml";;
 *
 * (Re-typing the #use line will re-include the file, which is useful if you
 * make changes; if things aren't working as you expect, exit the toplevel
 * (#quit;;) and restart.)
 *
 * You can compile all tests from the command line using (all on one line):
 *   > ocamlc -warn-error A unix.cma oUnit.mli oUnit.ml hellocaml.mli hellocaml.ml hellocaml_test.ml
 * 
 * After compiling, it's safe to delete any .cmi or .cmo files. The resulting
 * executable will be in the current working directory.
 *
 * Be sure to compile before submitting your assignment! Remember that
 * although we will grade assignments that fail unit tests, we will _not_
 * accept assignments that do not compile.
 *)

(*
 * All regions requiring your input are marked FILL IN HERE. If you can't
 * find any more instances of FILL IN HERE in either hellocaml.ml or
 * hellocaml.mli, you've provided an answer to every exercise. *)

(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(* PART 1                                                                     *)
(*                                                                            *)
(******************************************************************************)

(* First, we'll open some useful modules. 'open' allows you to use the types
 * and values defined in a particular module without having to retype that
 * module's name. It's a lot like Java's 'import'. *)

open Format (* for pretty printing *)
(* open Assert *)
(*
(* Here are some declarations of test names. These tests will fail by default,
 * but you will uncomment passing ones below. The >:: syntax comes from the
 * OUnit module. *)
let failure_test = "failure" >:: (fun () -> failwith "incomplete assignment")
let test_emaybe : test = failure_test
let test_get_unique_name : test = failure_test
let test_factorial : test = failure_test
let test_fold_left : test = failure_test
let test_rev_map : test = failure_test
let test_hanoi : test = failure_test
let test_hanoi_test : test = failure_test
let test_int32_comps : test = failure_test
let test_printf : test = failure_test
let test_hashtbl : test = failure_test
let test_trees : test = failure_test

(******************************************************************************)
(* Basic types                                                                *)
(******************************************************************************)
(* In class, the following representation of the natural numbers was
 * presented: *)
type nat = Zero | Succ of nat

(* Note that types always begin with lower-case letters. Constructors always
 * begin with upper-case letters. You also saw this definition for lists of
 * ints: *)
type intlist = Nil | Cons of int * intlist

(* You can add type parameters to types to make them generic. Type parameters
 * start with a '. When writing down a parameterized type, the types you're
 * instantiating the parameters to come before the type name (as in
 * ['t anylist] below). *)
type 't anylist = Nil | Cons of 't * ('t anylist)

(* Now we can define lists of ints and bools in terms of anylist: *)
type intlist' = int anylist
type boollist' = bool anylist

(* A type can take more than one type parameter-- just separate the type
 * variable names with commas. *)
type ('t,'u) rootlist = RNil of 'u | RCons of 't * (('t,'u) rootlist)
type intboolrootlist = (int,bool) rootlist

(* EXERCISE: give a definition for the emaybe type, which has one type
 * parameter 't and contains the constructor ENone (which has no arguments)
 * and the constructor ESome (which has one argument of type 't). *)
 
(* UNCOMMENT and FILL IN HERE

let test_emaybe : test =
  "test_emaybe" >:: (fun () ->
    ignore ENone;
    ignore (ESome "Does this compile?");
    ())
UNCOMMENT *)

(* If you want to run test_emaybe in the toplevel, type
 *   > run_test_tt test_emaybe;;
 * emaybe is almost exactly the builtin OCaml type [option], which is used
 * as the return type from functions that don't always return something
 * meaningful. *)

(* OCaml provides many other base types; some of these have special
 * semantics. [ref] is one such type. (Somewhat confusingly, [ref] is also
 * a function that returns a new reference cell.) *)
let int_cell : int ref = ref 0

(* int_cell is now a reference cell containing an int value. You can get the
 * value out of the reference cell using the ! operator: *)
let int_cell_val : int = !int_cell

(* You can also mutate the contents of the cell using (:=): *)
let int_set_result : unit = int_cell := 42

(* Of course, using mutable state is considered bad form in a functional
 * language. There are cases, though, where most people raise no argument--
 * like generating unique names. *)

(* EXERCISE: complete the definition of the get_unique_name function, which
 * increments the value stored at int_cell and returns that incremented
 * value. You can use the ; operator to sequence operations. *)
(* UNCOMMENT and FILL IN HERE
let get_unique_name () : int = ...

let test_get_unique_name : test = "test_get_unique_name" >:: (fun () ->
  int_cell := 0;
  "first name <> 1" @? (get_unique_name () = 1);
  "next name <> 2" @? (get_unique_name () = 2))
UNCOMMENT *)

(* Note the extra () argument to get_unique_name-- this extra unit value
 * has no semantic meaning to the function, but is used to keep OCaml from
 * evaluating the function immediately. If it were not there, then
 * get_unique_name would have the type int (instead of unit -> int)-- and you
 * could only get one unique name! *)

(* While you can get pretty far with reference types and tuples, sometimes
 * you want a little more structure-- if a tuple has four or more elements,
 * it can get rather difficult to remember the meaning of each. For this
 * case, OCaml provides records: *)
type sales_rolodex = {
  rx_name : string;
  rx_address : string;
  rx_zip : int option;
  mutable rx_widgets_sold : int
}

(* Records can have mutable and immutable fields. Record field names must
 * be unique within a module-- so it may be helpful to add prefixes to them
 * (here, rx_). Creating a record requires that you instantiate all fields: *)
let ben : sales_rolodex = {
  rx_name = "Benjamin Franklin";
  rx_address = "University of Pennsylvania";
  rx_zip = Some 19104;
  rx_widgets_sold = 0
}

(* You can also create a record by copying fields from another record of
 * the same type: *)
let ben' : sales_rolodex =
    { ben with rx_address = "Paris, France"; rx_zip = None }

(* (is equivalent to) *)
let ben'' : sales_rolodex = {
  rx_name = ben.rx_name;
  rx_address = "Paris, France";
  rx_zip = None;
  rx_widgets_sold = ben.rx_widgets_sold
}

(* You can access the values of fields with the familiar . operator: *)
let ben_name : string = ben.rx_name
let ben_widgets_sold : int = ben.rx_widgets_sold

(* ... and you can assign to mutable fields using (<-): *)
let _ = ben.rx_widgets_sold <- 42

(* ben.rx_widgets_sold and ben'.rx_widgets_sold are different references
 * (look closely at ben'', the full specification for ben'). Hence,
 * ben'.rx_widgets_sold is still 0. *)

(* There is no difference between a reference and a record with
 * one mutable field (and in fact reference cells are implemented as
 * mutable records): *)
let int_ref' : int ref = { contents = 43 }

(******************************************************************************)
(* Pattern Matching                                                           *)
(******************************************************************************)
(* Tagged unions and tuples would not be very useful if you could not access
 * the data they contain. Tuples are easy to break open: *)
let some_tuple : (string * int) = ("lobster", 4)

let (lobster,number_four) = some_tuple  (* Patterns can usually appear where
                                         * variables are declared. *)
let print_string_int ((s,i) : (string * int)) =
  Printf.printf "(\"%s\", %d)\n" s i
let _ = print_string_int some_tuple

(* Sometimes you just don't care about a particular member of a tuple (or even
 * a particular argument of a function). In that case, use the _ operator: *)
let (lobster,_) = some_tuple

(* Tagged unions are a little trickier to pick apart because they contain
 * data that depends on their runtime tag. Because of this, you have to
 * provide code for each possible branch: *)
type some_union_ty = True | False | FileNotFound of string

let string_of_some_union_ty (t : some_union_ty) : string = match t with
| True -> "True"
| False -> "False"
| FileNotFound s -> "FileNotFound " ^ s

(* You can provide a default case using _-- but be careful where you put it,
 * because patterns are matched from top to bottom. (If the _ case were at
 * the top, the following function would always return false.) *)
let bool_of_some_union_ty (t : some_union_ty) : bool = match t with
| True -> true
| _ -> false

(* Patterns can be arbitrarily complicated... *)
let ((lobster',_),(_,number_four')) = (some_tuple, some_tuple)

(* ... and can even contain Boolean guard conditions. Take care with the
 * order you leave cases in! *)
let string_of_some_union_ty' (t : some_union_ty) : string = match t with
| True -> "True"
| False -> "False"
| FileNotFound s when s = "" -> "FileNotFound, but we don't know which one"
| x -> string_of_some_union_ty x

(* It is an error to leave out a pattern case. If you compile your programs
 * with all warnings (as is the default when using OMake), the compiler should
 * warn you of this mistake. *)

(******************************************************************************)
(* Recursion                                                                  *)
(******************************************************************************)
(* When defining a type or value in OCaml, you can mention any type or value
 * that has already been defined. When defining a type t, you are also allowed
 * to mention t in its definition (as we did with most types above-- [nat]
 * has a constructor Succ which mentions [nat]). Sometimes, though, you may
 * need to define mutually recursive types like the following: *)
type pet = {
  pet_name : string;
  pet_owner : person
}
and person = {
  person_name : string;
  mutable person_pets : pet list
}

let ueno : person = { person_name = "H. Ueno"; person_pets = [] }
let hachiko : pet = { pet_name = "Hachiko"; pet_owner = ueno }
let _ = ueno.person_pets <- [hachiko]

(* Recursion in function declarations must be made explicit with [let rec]: *)
let rec count_to_ten (starting_from : int) : unit =
  if starting_from >= 10 then () else count_to_ten (starting_from + 1)

(* Doing all of this recursion can be expensive in stack space at runtime.
 * It's sometimes possible to make a very simple change that allows the
 * compiler to turn your recursion into a loop-- when a function's result
 * depends only on the result of a call to another function: *)

let rec silly (n:int) : int = if n <= 0 then 0 else silly (n - 1)

(* the compiler will refrain from making an extra function call (the 'tail
 * call') and re-use existing stack resources. *)
 
(* EXERCISE: Rewrite [factorial_tail] to enable the compiler to eliminate the
 * tail call. The definition from class is given below. You are likely
 * to want to declare a helper recursive function inside the body of your
 * [factorial] with two arguments-- the first being x as below, and the
 * second being an accumulator that stores the eventual result of the call. *)
let rec factorial_tail (x:int) : int =
  if x <= 0 then 1 else x * factorial_tail (x - 1)

(* UNCOMMENT and FILL IN HERE
let factorial (x:int) : int = ...

let test_factorial : test = "test_factorial" >::: [
  "-1" >:: (fun _ -> assert_equal ~printer:string_of_int
      (factorial_tail (-1)) (factorial (-1)));
  "0" >:: (fun _ -> assert_equal ~printer:string_of_int
      (factorial_tail 0) (factorial 0));
  "1" >:: (fun _ -> assert_equal ~printer:string_of_int
      (factorial_tail 1) (factorial 1));
  "6" >:: (fun _ -> assert_equal ~printer:string_of_int
      (factorial_tail 6) (factorial 6));
]
UNCOMMENT *)

(* Mutual recursion in function declarations looks just like mutual recursion
 * in type declarations: *)
let rec is_even (n:nat) : bool = match n with
  | Succ x -> is_odd x
  | Zero -> true
and is_odd (n:nat) : bool = match n with
  | Succ x -> is_even x
  | Zero -> false

(******************************************************************************)
(* Exceptions                                                                 *)
(******************************************************************************)
(* OCaml exceptions are an important part of the language-- and unlike Java or
 * C++, their use in regular control flow is encouraged. (Many search and
 * lookup functions in the standard library raise the [Not_found] exception
 * rather than return an [option]). *)
 
(* Declaring a new exception is like adding a new tag to the 'exn' tagged
 * union: *)
exception InsufficientFunds of int
exception BadPIN

(* Raising and catching exceptions is fairly simple, with catching boiling
 * down to pattern matching: *)
let _ =
  try
    raise (InsufficientFunds 42)
  with
  | InsufficientFunds i -> Printf.sprintf "You need %d more!" i

(* Uncaught exceptions trickle outward until they're caught: *)
let _ =
  try (
    try
      raise BadPIN
    with
    | InsufficientFunds i -> Printf.sprintf "You need %d more!" i
  )
  with
  | BadPIN -> Printf.sprintf "Bad PIN"

(******************************************************************************)
(* Lists                                                                      *)
(******************************************************************************)
(* The standard library contains many useful functions for operating over
 * lists. Here are a few: *)

type grocery = (string * int)

(* A grocery list of item, price (cents) pairs. *)
let groceries : grocery list =
  [("milk", 100); ("eggs", 250); ("orange juice", 240)]

(* We can add items to the list with cons, an O(1) operation: *)
let groceries' : grocery list =
  ("gum", 50) :: groceries

(* Or we can concatenate whole lists together (costing O(n) time): *)
let groceries'' : grocery list =
  [("flan", 100); ("gouda", 650)] @ groceries

(* We can print out each item on the list...
 *   iter : ('a -> unit) -> 'a list -> unit *)
let _ =
  List.iter (fun (item, cost) -> Printf.printf "%s: %d" item cost)

(* We can generate a new list where every item costs half as much...
 *   map : ('a -> 'b) -> 'a list -> 'b list *)
let sale : grocery list -> grocery list =
  List.map (fun (item, cost) -> (item, cost / 2))

(* We can sum the costs on the list...
 *   fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a *)
let total : grocery list -> int =
  List.fold_left (fun subtotal (_, cost) -> subtotal + cost) 0

(* It's important to keep track of the tail-recursiveness of list operations
 * and to remember what your output will look like. For instance, the following
 * is equivalent to List.rev (which reverses a list): *)
let rev' (l : 'a list) : 'a list =
  List.fold_left (fun sublist next -> next :: sublist) [] l

(* Of the operations above, List.map is not tail recursive. List.rev_map,
 * which works like List.map, is tail recursive but returns a reversed list.
 * List.fold_right is a non-tail-recursive variant of List.fold_left above
 * and operates on the elements of the list in reverse order-- for example,
 * we could write an identity function on lists using List.fold_right: *)
let idlist (l : 'a list) : 'a list =
  List.fold_right (fun next sublist -> next :: sublist) l []
  
(* Note how the order of the arguments changes to reflect the direction
 * the function takes when walking over the list. *)
 
(* Pattern matching on lists looks just like constructing lists. Here's some
 * code for [iter]: *)
let rec iter' (f : 'a -> unit) (l : 'a list) : unit =
  match l with
  | hd :: tl -> f hd; iter' f tl
  | [] -> ()

(* EXERCISE: Provide code for fold_left', a tail-recursive function equivalent
 * to List.fold_left. (The documentation for module List states that:
 *   List.fold_left f a [b1; ...; bn] is f (... (f (f a b1) b2) ...) bn.
 * Do not call any functions aside from those you declare. *)
(* UNCOMMENT and FILL IN HERE
let rec fold_left' (f : 'a -> 'b -> 'a) (start : 'a) (l : 'b list) : 'a =
  ...

let test_fold_left : test =
  "test_fold_left" >:: (fun () -> assert_equal "hello"
      (fold_left' (fun p n -> p ^ n) "h" ["e";"l";"lo"]))
UNCOMMENT *)

(* EXERCISE: Provide code for rev_map', a tail-recursive function equivalent
 * to List.rev_map. The documentation for rev_map' states that:
 *   List.rev_map f l gives the same result as List.rev (List.map f l), but is
 *   tail-recursive and more efficient.
 * and:
 *   List.map f [a1; ...; an] applies function f to a1, ..., an, and builds
 *   the list [f a1; ...; f an]  with the results returned by f. Not
 *   tail-recursive.
 * Do not call any functions aside from those you declare-- and in particular,
 * do not define rev_map in terms if fold_left. *)
(* UNCOMMENT and FILL IN HERE
let rev_map' (f : 'a -> 'b) (l : 'a list) : 'b list =
  ...
UNCOMMENT *)

(* EXERCISE: Now provide code for rev_map'', which is rev_map' (which is
 * rev_map) but defined in terms of fold_left'. This function should be
 * one line long (not counting the let). *)
(* UNCOMMENT and FILL IN HERE
let rec rev_map'' (f : 'a -> 'b) (l : 'a list) : 'b list =
  ...

let test_rev_map : test =
  let plat s =
    if String.length s = 0 then s else
      let fch = Char.lowercase (String.get s 0) in
      match fch with
      | 'a' | 'e' | 'i' | 'o' | 'u' -> s ^ "way"
      | _ -> Printf.sprintf "%s%cay" (String.sub s 1 (String.length s - 1)) fch
  in let test_arr = ["cons";"is";"pretty";"handy"]
  in let resl_arr = ["andyhay";"rettypay";"isway";"onscay"]
  in "test_rev_map" >::: [
    "rev_map'" >:: (fun () -> assert_equal resl_arr (rev_map' plat test_arr));
    "rev_map''" >:: (fun () -> assert_equal resl_arr (rev_map' plat test_arr))
  ]
UNCOMMENT *)

(******************************************************************************)
(*                                                                            *)
(* PART 2                                                                     *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(* Interlude of Hanoi (or: CIS 552 all over again)                            *)
(******************************************************************************)

(* EXERCISE: Throughout this file, we've given you some unit tests to check
 * your work. In future assignments, we will expect you to write your own
 * tests in addition to those that we provide. As a warm up, complete both
 * this problem and its test.
 *
 * In the Towers of Hanoi puzzle, you are given three pegs. On the first
 * peg is a series of discs; these discs are all of diameters of decreasing
 * size, with the largest on the bottom and the smallest on the top. You may
 * move the top disc from any peg to the top of any other peg, provided that
 * the disc on top of the new peg is larger than the disc you're trying to
 * move. Your goal is to move all of the discs from the leftmost peg to
 * the rightmost peg in 2^n-1 moves, where n is the number of discs.
 *
 * Write a function hanoi that constructs a list of tuples of type (peg*peg)
 * (indicating (peg-from,peg-to)). The first move should be at the head of the
 * list, while the last move should be at the tail of the list. (There are
 * plenty of solutions for this online, but try to come up with one on your
 * own if you have a moment.) Even if you do look it up, try to build the move
 * list using only (::) and a single List.rev (executed once). *)

type peg = PLeft | PMiddle | PRight
type hanoimove = (peg * peg)

(* UNCOMMENT and FILL IN HERE
let hanoi (n:int) : hanoimove list =
  ...
UNCOMMENT *)

(* Now write a function test_hanoi_aux that takes a list of moves and verifies
 * that those moves represent a legal Towers of Hanoi solution of the
 * required length. Return false if the pegs are not in the right state
 * or the number of moves is incorrect at the end of the game; define and
 * raise an exception named IllegalMove and raise it should the move list
 * contain an illegal move. (You must always raise this exception in the case
 * of an illegal move, even when other error conditions (too few moves; wrong
 * ending state) exist.) Try to define this function's main body in
 * terms of List.fold_left and without any imperative updates. *)

(* Here are some utility functions that might come in handy while debugging: *)
let print_int_list (l:int list) : unit =
  Printf.printf "[";
  List.iter (fun i -> Printf.printf "%d;" i) l;
  Printf.printf "]\n"

let string_of_peg : peg -> string =
  function PLeft -> "l" | PMiddle -> "m" | PRight -> "r"

let print_move ((f,t) : (peg*peg)) : unit =
  Printf.printf "from %s to %s\n" (string_of_peg f) (string_of_peg t)

(* UNCOMMENT and FILL IN HERE


let test_hanoi_aux (n:int) (m:hanoimove list) : bool =
  let required_length = (1 lsl n) - 1 in
  ...

let test_hanoi : test =
  let test' n =
    let testname = (Printf.sprintf "%d discs" n) in
    testname >:: (fun () -> assert_bool testname (test_hanoi_aux n (hanoi n)))
  in "Towers of Hanoi" >::: [test' 0; test' 1; test' 2; test' 3; test' 5]

let test_hanoi_test : test = "test_hanoi_test" >::: [
  "ok0" >:: (fun () -> assert_bool "ok0" (test_hanoi_aux 0 []));
  "ok1" >:: (fun () -> assert_bool "ok1" (test_hanoi_aux 1
      [(PLeft,PRight)]));
  "ok3" >:: (fun () -> assert_bool "ok3" (test_hanoi_aux 3
      [(PLeft, PRight); (PLeft, PMiddle); (PRight, PMiddle); (PLeft, PRight);
       (PMiddle, PLeft); (PMiddle, PRight); (PLeft, PRight)]));
  "bad_toomany" >:: (fun () -> assert_bool "bad_toomany" (not (test_hanoi_aux 3
      [(PLeft, PRight); (PLeft, PMiddle); (PRight, PMiddle); (PLeft, PRight);
       (PMiddle, PLeft); (PMiddle, PRight); (PLeft, PRight); (PRight, PLeft);
       (PLeft, PRight)])));
  "bad_badend" >:: (fun () -> assert_bool "bad_badend" (not (test_hanoi_aux 3
      [(PLeft, PMiddle); (PLeft, PRight); (PMiddle, PRight); (PLeft, PMiddle);
       (PRight, PLeft); (PRight, PMiddle); (PLeft, PMiddle)])));
  "bad_toofew" >:: (fun () -> assert_bool "bad_toofew" (not (test_hanoi_aux 3
      [(PLeft, PRight); (PLeft, PMiddle); (PRight, PMiddle); (PLeft, PRight);
       (PMiddle, PLeft)])));
  "bad_crush" >:: (fun () -> assert_raises IllegalMove
      (fun () -> test_hanoi_aux 3 ([(PLeft, PRight); (PLeft, PMiddle);
          (PRight, PMiddle); (PLeft, PMiddle); (PLeft, PRight);
          (PMiddle, PLeft); (PMiddle, PRight)])));
  "bad_none" >:: (fun () -> assert_raises IllegalMove
      (fun () -> test_hanoi_aux 3 ([(PLeft, PRight); (PLeft, PMiddle);
          (PRight, PMiddle); (PLeft, PRight); (PLeft, PRight);
          (PMiddle, PRight); (PMiddle, PLeft)])));
  "bad_none2" >:: (fun () -> assert_raises IllegalMove
      (fun () -> test_hanoi_aux 1 ([(PRight,PLeft)])))
]
UNCOMMENT *)

(******************************************************************************)
(* The Standard Library                                                       *)
(******************************************************************************)

(* OCaml's standard library, documented at
 *   http://caml.inria.fr/pub/docs/manual-ocaml/libref/index.html
 * contains most of the base functionality that you'll need to complete
 * assignments. We've gone over most of the List module and you've probably
 * seen some other functions peeking out in places. Here are a couple of
 * modules that you're likely to need when completing assignments. *)

(* The OCaml int type is actually 31 bits wide. If you want to use a proper
 * 32-bit integer, you need to use the int32 type. Int32 literals look just
 * like int literals, but with a lower-case l at the end: *)
let int32_42 : int32 = 42l

(* The Int32 module defines operations on int32 types: *)
let int32_two : int32 = Int32.add 1l 1l

(* EXERCISE: since it can be painful to use function names instead of
 * operators for common binary operations, you might want to declare some
 * new operators. Fill in the definitions for <@, >@, <=@, and >=@, which
 * act like >, <, <=, and >= over int32s. *)
(* UNCOMMENT and FILL IN HERE
let (<@) (a : int32) (b : int32) : bool = ...
let (<=@) (a : int32) (b : int32) : bool = ...
let (>@) (a : int32) (b : int32) : bool = ...
let (>=@) (a : int32) (b : int32) : bool = ...


let test_int32_comps : test = "test_int32_comps" >::: [
  "<@" >:: (fun () -> assert_equal false (3l <@ 2l));
  "<@'" >:: (fun () -> assert_equal true (2l <@ 3l));
  "<=@" >:: (fun () -> assert_equal true (3l <=@ 3l));
  "<=@'" >:: (fun () -> assert_equal true (2l <=@ 3l));
  ">@" >:: (fun () -> assert_equal true (3l >@ 2l));
  ">@'" >:: (fun () -> assert_equal false (2l >@ 3l));
  ">=@" >:: (fun () -> assert_equal true (3l >=@ 3l));
  ">=@'" >:: (fun () -> assert_equal false (2l >=@ 3l))
]
UNCOMMENT *)

(* Module Printf allows for C-style (but still typesafe) format strings.
 * It works with a little bit of magic compiler support for those strings.
 * You can use it to print directly to the terminal, as: *)
let _ = Printf.printf "Hello, world! 1 + 2 = %d\n" 3

(* or you can use it to build strings: *)
let a_string : string = Printf.sprintf "1 2 %d %d %s" 3 4 "strings!"

(* You'll probably want to remember these type tags (the characters that
 * come after the % and determine the type of that argument to the format
 * string):
 *   %d: int (in base 10)
 *   %x: int (in hexadecimal)
 *   %s: string
 *   %B: boolean
 *   %ld: int32 (in base 10)
 *   %lx: int32 (in hexadecimal) *)
 
(* EXERCISE: write a format string such that the output from the call to
 * sprintf equals exactly the example string. You'll have to check the
 * documentation to see how to pad out zeros. *)
(* UNCOMMENT and FILL IN HERE
let format_string : ('a,'b,'c) format = "..."
let example_string : string = "000a 42 true end"
let output_string : string = Printf.sprintf format_string
    10 42l true "end"

let test_printf : test = "test_printf" >:: (fun () ->
    assert_equal example_string output_string)
UNCOMMENT *)

(* Module Hashtbl gives you easy-to-use _imperative_ association lists.
 * Unlike most other OCaml data structures, Hashtbls are mutable-- so be
 * careful when you use them! *)

(* A Hashtbl will associate any type to any other type (thanks to the
 * polymorphic function Hashtbl.hash). When you create the Hashtbl, you must
 * provide it with a guess of the table's size. It's not a problem if you
 * guess incorrectly-- your program just won't perform as well. *)
let string_to_int : (string,int) Hashtbl.t = Hashtbl.create 6
let nat_to_string : (nat,string) Hashtbl.t = Hashtbl.create 3

(* Add new entries to the table with Hashtbl.add. *)
let _ = Hashtbl.add string_to_int "one" 1

(* It's not an error to add more than one entry with the same key... *)
let _ = Hashtbl.add string_to_int "one" 2

(* But Hashtbl.find will return the last value added for a particular key. *)
let int_two : int = Hashtbl.find string_to_int "one"

(* Because of this, you'll usually want to use Hashtbl.replace instead of
 * Hashtbl.add. (Hashtbl.replace only replaces one or zero bindings-- if
 * there are more than two bindings for a key, Hashtbl.replace will still
 * leave the key multiply bound.) *)
let _ = Hashtbl.replace string_to_int "two" 3
let _ = Hashtbl.replace string_to_int "two" 2
let int_two' : int = Hashtbl.find string_to_int "two"

(* EXERCISE: write a function defines_foo that, for any Hashtbl.t with string
 * keys, returns true if the table contains a key with the value "foo". You
 * must give the entire definition, including a full type signature for the
 * let. Write two versions-- defines_foo_mem should use Hashtbl.mem, while
 * defines_foo_find should use Hashtbl.find. (You can use [ignore], defined
 * in module Pervasives (which is automatically opened), to coerce any value
 * to Unit.) *)
(* UNCOMMENT and FILL IN HERE
let defines_foo_mem (ht : (string,'a) Hashtbl.t) : bool =
  ...

let defines_foo_find (ht : (string,'a) Hashtbl.t) : bool =
  ...

let test_hashtbl : test =
  let foo_table = Hashtbl.create 1 in
  let bar_table = Hashtbl.create 1 in
  Hashtbl.add foo_table "foo" ();
  Hashtbl.add bar_table "bar" ();
  "test_hashtbl" >::: [
    "has_foo_m" >:: (fun () -> assert_equal true (defines_foo_mem foo_table));
    "has_foo_f" >:: (fun () -> assert_equal true (defines_foo_find foo_table));
    "has_bar_m" >:: (fun () -> assert_equal false (defines_foo_mem bar_table));
    "has_bar_f" >:: (fun () -> assert_equal false (defines_foo_find bar_table));
  ]
UNCOMMENT *)

(* Arrays (from module Array) give you a fixed-length array that can be
 * indexed in O(1) time and imperatively updated. OCaml supports array
 * literals: *)
let int_arr : int array = [| 1; 2; 3; 4 |]

(* Arrays support operations like map and fold_left. *)
let int2_arr : int array = Array.map (fun i -> i * 2) int_arr
let int_arr_sum : int = Array.fold_left (fun p n -> p + n) 0 int_arr

(* You can index an array using Array.get or the special a.(n) syntax: *)
let int_arr_1 : int = int_arr.(1)

(* You can update the array using a combination of the <- syntax from records
 * and the a.(n) syntax for array lookups: *)
let _ = int2_arr.(0) <- 42

(******************************************************************************)
(* Modules                                                                    *)
(******************************************************************************)
(* Modules are OCaml's highest level of program organization.
 * You've already seen modules that cover whole files-- this file, in fact,
 * is the implementation of the module Hellocaml. Its interface is in the file
 * Hellocaml.mli. This file limits the values and types that face the public.
 * You can also declare a module within another module's implementation. *)

module Counter = struct
  let current_ctr = ref 0
  let get_current_ctr () : int = !current_ctr
  let set_current_ctr (i : int) : unit = current_ctr := i
end

let _ = Counter.set_current_ctr 36
let int_thirtysix = Counter.get_current_ctr ()

(* Just as you can hide implementation details using .mli files, so can you
 * hide module implementation details using signatures: *)
module Counter' : sig
  val get_current_ctr : unit -> int
  val set_current_ctr : int -> unit
end = struct
  let current_ctr = ref 0
  let get_current_ctr () : int = !current_ctr
  let set_current_ctr (i : int) : unit = current_ctr := i
end

(* Much more information on the module system can be found in the OCaml manual,
 * including methods for parameterizing modules by other modules, at
 *   http://caml.inria.fr/pub/docs/manual-ocaml/manual004.html *)

(******************************************************************************)
(* A Module for Trees                                                         *)
(******************************************************************************)
(* EXERCISE: Create a module called Int32ST that keeps tracks of sets of
 * ordered values using unbalanced binary search trees. Provide both a
 * signature and an implementation. The module should define:
 *   - one type called t (which is the type of the set)
 *   - one non-functional value called empty (of type t, representing
 *     an empty set)
 *   - the function mem, which takes a set followed by an element and returns
 *     a bool that is true of the element exists in that set
 *   - the function insert, which takes a set followed by an element and
 *     returns the original set if the element is already present or a new
 *     set containing the elements of the original set plus the element. *)

(* UNCOMMENT and FILL IN HERE
module Int32ST : sig
  ...
end = struct
  ...
end

let test_trees : test = "test_trees" >::: [
  "empty" >:: (fun () ->
    assert_equal false (Int32ST.mem Int32ST.empty 1l)
  );
  "test1" >:: (fun () ->
    let t = List.fold_left Int32ST.insert Int32ST.empty [1l;0l;2l] in
    assert_equal true (Int32ST.mem t 1l);
    assert_equal true (Int32ST.mem t 0l);
    assert_equal true (Int32ST.mem t 2l);
    assert_equal false (Int32ST.mem t (-1l))
  );
  "test2" >:: (fun () ->
    let t = List.fold_left Int32ST.insert Int32ST.empty [1l;2l;3l;4l;5l] in
    assert_equal true (Int32ST.mem t 1l);
    assert_equal true (Int32ST.mem t 2l);
    assert_equal true (Int32ST.mem t 3l);
    assert_equal true (Int32ST.mem t 4l);
    assert_equal true (Int32ST.mem t 5l)
  );
  "test3" >:: (fun () ->
    let t = List.fold_left Int32ST.insert Int32ST.empty [1l;2l;3l;5l;6l;4l] in
    assert_equal true (Int32ST.mem t 1l);
    assert_equal true (Int32ST.mem t 2l);
    assert_equal true (Int32ST.mem t 3l);
    assert_equal true (Int32ST.mem t 4l);
    assert_equal true (Int32ST.mem t 5l);
    assert_equal true (Int32ST.mem t 6l)
  )
]
UNCOMMENT *)

(* Finally, expose some more functionality from this module to others by
 * adding entries to the interface file. Expose the type sales_rolodex,
 * the function defines_foo_find, and the module Int32ST. *)
(* FILL IN HERE -- delete this line and fill in inside hellocaml.mli *)

(******************************************************************************)
(* Equality (FYI)                                                             *)
(******************************************************************************)

(* The documentation for the Pervasives module defines the operation of the
 * = operator as:
 *   e1 = e2 tests for structural equality of e1 and e2. Mutable structures
 *   (e.g. references and arrays) are equal if and only if their current
 *   contents are structurally equal, even if the two mutable objects are not
 *   the same physical object. Equality between functional values raises
 *   Invalid_argument. Equality between cyclic data structures does not
 *   terminate.
 *
 * 'structural equality' means that OCaml will walk over the tree structures
 * of your values to determine their equality. If your values are really
 * cyclic graphs, then this simple walk will never terminate.
 *
 * The == operator, on the other hand, is a more familiar reference equality:
 *   e1 == e2 tests for physical equality of e1 and e2. On integers and
 *   characters, physical equality is identical to structural equality. On
 *   mutable structures, e1 == e2 is true if and only if physical modification
 *   of e1 also affects e2. On non-mutable structures, the behavior of (==)
 *   is implementation-dependent; however, it is guaranteed that e1 == e2
 *   implies compare e1 e2 = 0.
 *
 * The take-away from this should be to be careful with equality over any value
 * more complicated than an int, string or zero-argument constructor. *)

(******************************************************************************)

let all_tests = "all tests" >::: [
  test_emaybe;
  test_get_unique_name;
  test_factorial;
  test_fold_left;
  test_rev_map;
  test_hanoi;
  test_hanoi_test;
  test_int32_comps;
  test_printf;
  test_hashtbl;
  test_trees
]
*)
