(* 1. The function subset a b returns true iff a ⊆ b *)

let rec subset a b =
  match a with 
  | [] -> true
  | h :: t -> List.mem h b && subset t b


(* 2. The function equal_sets a b returns true iff the represented sets are equal. *)
let equal_sets a b = 
  subset a b && subset b a


(* 3. The function set_union a b returns a list representing a U b. *)
let rec set_union a b = 
  match a with
  | [] -> b
  | h :: t -> set_union t (h::b)


(* 4. The function set_all_union a returns a list representing ∪[x ∈ a]x 
Go through all elements and apply set_union to all element, use the built 
in function fold_left *)
let set_all_union a = 
  List.fold_left set_union [] a


(* 5. Russell's Paradox involves asking whether a set is a member of itself. 
Write a function self_member s that returns true iff the set represented by 
s is a member of itself, and explain in a comment why your function is correct; 
if it's not possible to write such a function in OCaml, explain why not in a comment. *)

(* This function is impossible to implement in OCaml because the type does match. For 
example, for set s with type 'a, it would be to be list 'a to contain itself, which is  
impossible to do in OCaml due to its type check *)


(* 6. The function computed_fixed_point eq f x returns the computed fixed point for 
f with respect to x, assuming that eq is the equality predicate for f's domain.*)
let rec computed_fixed_point eq f x = 
  if eq x (f x) then x
  else computed_fixed_point eq f (f x)


(* 7. The function computed_periodic_point eq f p x returns the computed periodic 
point for f with period p and with respect to x, assuming that eq is the equality 
predicate for f's domain. *)
let rec computed_periodic_point eq f p x = 
  let rec apply f p x = 
    if p > 0 then apply f (p-1) (f x)
    else x
  in
  if eq x (apply f p x) then x
  else computed_periodic_point eq f p (f x)


(* 8. The function whileseq s p x returns the longest list [x; s x; s (s x); ...] 
such that p e is true for every element e in the list. *)
let rec whileseq s p x = 
  if (p x) then (x::(whileseq s p (s x)))
  else []


(* 9. The function filter_blind_alleys g returns a copy of the grammar g with 
all blind-alley rules removed. This function preserve the order of rules. *)
type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal

(* aux function checking if an element is contained in a list*)
let rec contain_element e l = 
  match l with 
  |[] -> false
  | h :: t -> (e = h) || (contain_element e t)

(* aux func checking whether a symbol is terminable*)
let symbol_terminability s l =
  match s with
  | T terminal -> true
  | N nonterminal -> contain_element s l

(* aux func check rhs only contains terminable symbols*)
let rec rhs_terminability rhs l =
  match rhs with
  | [] -> true
  | h :: t -> if (symbol_terminability h l) then (rhs_terminability t l)
              else false

(* aux func return ('a, 'b) symbol list with all terminable symbols in rules *)
let rec terminable_symbol_list rules l =
  match rules with
  | [] -> l
  | (symbol, rhs)::t -> if (rhs_terminability rhs l) 
                          then (terminable_symbol_list t ((N symbol)::l))
                          else (terminable_symbol_list t l)


(* aux func returns a tuple with rules, list containing terminalb symbols*)
let rules_symbols (rules, l) =
  (rules, terminable_symbol_list rules l)

(* aux func check whether two results from the prev func are the same*)
let equal_rules_symbols (r1, l1) (r2, l2) =
  equal_sets l1 l2

(* aux func to generate tuple with rules and terminable symbols *)
let final_list r l =
  computed_fixed_point (equal_rules_symbols) (rules_symbols) (r, l)

(* aux func check rhs only contain terminable symbol for all rules
remove rules with unterminable rhs*)
let rec remove_rules (r, l) = 
  match r with
  | (s, rhs) :: t -> if (rhs_terminability rhs l) 
                        then ((s, rhs)::(remove_rules (t, l)))
                      else (remove_rules (t, l))
  | [] -> []

(* final function *)
let filter_blind_alleys g =
  match g with
  | (start, rules) -> (start, (remove_rules (final_list rules [])))

(* 10. Supply at least one test case for each of the above functions in the style shown in the sample test cases below. 
When testing the function F, call the test cases my_F_test0, my_F_test1, etc. For example, for subset your first test case 
should be called my_subset_test0. Your test cases should exercise all the above functions, even though the sample test cases do not.*)

