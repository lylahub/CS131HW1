(* 1. The function subset a b returns true iff a ⊆ b *)
(* input:  a:'a list
            b:'a list
    output: bool
   type: val subset : 'a list -> 'a list -> bool = <fun>  *)
let rec subset a b =
  match a with 
  | [] -> true
  | h :: t -> List.mem h b && subset t b


(* 2. The function equal_sets a b returns true iff the represented sets are equal. *)
(* input:  a:'a list 
            b:'a list
    output: bool
    val equal_sets : 'a list -> 'a list -> bool = <fun> *)
let equal_sets a b = 
  subset a b && subset b a


(* 3. The function set_union a b returns a list representing a U b. *)
(* input:  a:'a list ; b:'a list
    output: 'a list
    val set_union : 'a list -> 'a list -> 'a list = <fun> *)
let rec set_union a b = 
  match a with
  | [] -> b
  | h :: t -> set_union t (h::b)


(* 4. The function set_all_union a returns a list representing ∪[x ∈ a]x Go through all elements and apply set_union to all element, use the built 
in function fold_left *)
(* input:  a:'a list list
    output: 'a list
    val set_all_union : 'a list list -> 'a list = <fun> *)
let set_all_union a = 
  List.fold_left set_union [] a


(* 5. Russell's Paradox involves asking whether a set is a member of itself. Write a function self_member s that returns true iff the set represented by s is a member of itself, and explain in a comment why your function is correct; if it's not possible to write such a function in OCaml, explain why not in a comment. *)

(* This function is impossible to implement in OCaml because the type does match. For example, for set s with type 'a, it would be to be list 'a to contain itself, which is impossible to do in OCaml due to its type check *)


(* 6. The function computed_fixed_point eq f x returns the computed fixed point for f with respect to x, assuming that eq is the equality predicate for f's domain.*)
(* input:  eq: 'a -> 'a -> bool = <fun>
            f: 'a -> 'a = <fun> 
            x: 'a 
    output: 'a 
    val computed_fixed_point : ('a -> 'a -> bool) -> ('a -> 'a) -> 'a -> 'a = <fun> *)
let rec computed_fixed_point eq f x = 
  if eq x (f x) then x
  else computed_fixed_point eq f (f x)


(* 7. The function computed_periodic_point eq f p x returns the computed periodic point for f with period p and with respect to x, assuming that eq is the equality predicate for f's domain. *)
(* input:  eq: 'a -> 'a -> bool = <fun> 
            f: 'a -> 'a = <fun>
            p: int
            x: 'a 
    output: 'a 
    val computed_periodic_point : ('a -> 'a -> bool) -> ('a -> 'a) -> int -> 'a -> 'a = <fun> *)
let rec computed_periodic_point eq f p x = 
  let rec apply f p x = 
    if p > 0 then apply f (p-1) (f x)
    else x
  in
  if eq x (apply f p x) then x
  else computed_periodic_point eq f p (f x)


(* 8. The function whileseq s p x returns the longest list [x; s x; s (s x); ...] such that p e is true for every element e in the list. *)
(* input:  s: 'a -> 'a = <fun> 
            p: 'a -> bool = <fun>
            x: 'a 
    output: 'b list 
    val whileseq : ('a -> 'a) -> ('a -> bool) -> 'a -> 'a list = <fun> *)
let rec whileseq s p x = 
  if (p x) then (x::(whileseq s p (s x)))
  else []


(* 9. The function filter_blind_alleys g returns a copy of the grammar g with all blind-alley rules removed. This function preserve the order of rules. *)

(* define type for symbol *)
type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal

(* aux function checking if an element is contained in a list*)
(* input:  elem:'a
            lst:'a list
    output: bool
    type: val is_in : 'a -> 'a list -> bool = <fun> *)
let rec contain_element e l = 
  match l with 
  |[] -> false
  | h :: t -> (e = h) || (contain_element e t)

(* aux func checking whether a symbol is terminable *)
(* input:  symbol: ('a, 'b) symbol 
            terminable_symbol_list: ('a, 'b) symbol list
    output: bool
    val is_symbol_terminable : ('a, 'b) symbol  -> ('a, 'b) symbol list -> bool = <fun> *)
let symbol_terminability s l =
  match s with
  | T terminal -> true
  | N nonterminal -> contain_element s l

(* aux func check rhs only contains terminable symbols*)
(* input:  rhs: ('a, 'b) symbol list
            terminable_symbol_list: ('a, 'b) symbol list
    output: bool
    val is_rhs_all_terminable : ('a, 'b) symbol list -> ('a, 'b) symbol list -> bool = <fun> *)
let rec rhs_terminability rhs l =
  match rhs with
  | [] -> true
  | h :: t -> if (symbol_terminability h l) then (rhs_terminability t l)
              else false

(* aux func return ('a, 'b) symbol list with all terminable symbols in rules *)
(* input:  rules: (('a, 'b) symbol * ('a, 'b) symbol list) list
            terminable_symbol_list: ('a, 'b) symbol list
    output: ('a, 'b) symbol list
    val construct_terminable_symbol_list : ('a * ('a, 'b) symbol list) list -> ('a, 'b) symbol list -> ('a, 'b) symbol list = <fun> *)
let rec terminable_symbol_list rules l =
  match rules with
  | [] -> l
  | (symbol, rhs)::t -> if (rhs_terminability rhs l) 
                          then (terminable_symbol_list t ((N symbol)::l))
                          else (terminable_symbol_list t l)


(* aux func returns a tuple with rules, list containing terminalb symbols*)
(* input:  (rules, terminable_symbol_list): ((('a, 'b) symbol * ('a, 'b) symbol list) list * ('a, 'b) symbol list)
   output: (rules, terminable_symbol_list): ((('a, 'b) symbol * ('a, 'b) symbol list) list * ('a, 'b) symbol list)
   val rules_with_terminable_symbol_list : ('a * ('a, 'b) symbol list) list * ('a, 'b) symbol list -> ('a * ('a, 'b) symbol list) list * ('a, 'b) symbol list = <fun> *)
let rules_symbols (rules, l) =
  (rules, terminable_symbol_list rules l)

(* aux func check whether two results from the prev func are the same*)
(* input:  (rules1, terminable_symbol_list1): ((('a, 'b) symbol * ('a, 'b) symbol list) list * ('a, 'b) symbol list)
            (rules2, terminable_symbol_list2): ((('a, 'b) symbol * ('a, 'b) symbol list) list * ('a, 'b) symbol list)
    output: bool
    val equal_terminable_symbol_list : 'a * 'b list -> 'c * 'b list -> bool = <fun> *)
let equal_rules_symbols (r1, l1) (r2, l2) =
  equal_sets l1 l2

(* aux func to generate tuple with rules and terminable symbols *)
(* input:  rules: (('a, 'b) symbol * ('a, 'b) symbol list) list
            terminable_symbol_list: ('a, 'b) symbol list
    output: ((('a, 'b) symbol * ('a, 'b) symbol list) list * ('a, 'b) symbol list)
    val final_terminable_symbol_list : ('a * ('a, 'b) symbol list) list -> ('a, 'b) symbol list -> ('a * ('a, 'b) symbol list) list * ('a, 'b) symbol list = <fun> *)
let final_list r l =
  computed_fixed_point (equal_rules_symbols) (rules_symbols) (r, l)

(* aux func check rhs only contain terminable symbol for all rules
remove rules with unterminable rhs*)
(* input:  (rules, terminable_symbol_list): ((('a, 'b) symbol * ('a, 'b) symbol list) list * ('a, 'b) symbol list)
    output: (('a, 'b) symbol * ('a, 'b) symbol list) list 
    val remove_bad_rules : ('a * ('b, 'c) symbol list) list * ('b, 'c) symbol list -> ('a * ('b, 'c) symbol list) list = <fun> *)
let rec remove_rules (r, l) = 
  match r with
  | (s, rhs) :: t -> if (rhs_terminability rhs l) 
                        then ((s, rhs)::(remove_rules (t, l)))
                      else (remove_rules (t, l))
  | [] -> []

(* final function *)
(* input:  g: ('a, 'b) symbol * (('a, 'b) symbol * ('a, 'b) symbol list) list
    output: ('a, 'b) symbol * (('a, 'b) symbol * ('a, 'b) symbol list) list
    val filter_blind_alleys : 'a * ('b * ('b, 'c) symbol list) list -> 'a * ('b * ('b, 'c) symbol list) list = <fun> *)
let filter_blind_alleys g =
  match g with
  | (start, rules) -> (start, (remove_rules (final_list rules [])))

