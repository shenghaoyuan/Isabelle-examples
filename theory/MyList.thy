theory MyList
  imports
    Main
begin

datatype 'a List =
  LNil |
  LCons 'a "'a List"

(**

datatype mynat =
  MyZero |
  MySuc (n: mynat) 

*)

(** how to represent an array [1;2;3] using List ?

step1:

step2:

step3:

 *)

(*
value "hd ([1,2,3]::nat list)"
value "hd ([]::nat list)"
*)


(**

datatype 'a option =
    None
  | Some (the: 'a)

definition my_system:: "... \<Rightarrow> 'a option" where

Safety Property:
lemma my_system_is_safe "pre_condition \<Longrightarrow> my_system ... \<noteq> None"
*)

(**r https://coq.inria.fr/doc/v8.9/stdlib/Coq.Lists.List.html#hd_error  *)
fun hd_error :: "'a List \<Rightarrow> 'a option" where
"hd_error LNil = None" |
"hd_error (LCons h t) = Some h"

value "hd_error ((LCons 1 (LCons 2 (LCons 3 LNil)))::nat List)"
value "hd_error (LNil::nat List)"

lemma hd_error_is_safe: "l \<noteq> LNil \<Longrightarrow> hd_error l \<noteq> None" sorry

axiomatization hd_default :: "'a List \<Rightarrow> 'a \<Rightarrow> 'a"

lemma hd_error_hd_default_some: "hd_error l = Some v \<Longrightarrow> hd_default l d_v = v" sorry

lemma hd_error_hd_default_none: "hd_error l = None \<Longrightarrow> hd_default l d_v = d_v" sorry

value "last ([1,2,3]::nat list)"
(*
value "last ([]::nat list)"
fun last_error :: "'a list \<Rightarrow> 'a option" where
definition last_error1 :: "'a list \<Rightarrow> 'a list option" where *)

axiomatization last_error   :: "'a List \<Rightarrow> 'a option"
axiomatization last_error1  :: "'a list \<Rightarrow> 'a list option"

axiomatization nth_error :: "'a List \<Rightarrow> nat \<Rightarrow> 'a option"
axiomatization length :: "'a List \<Rightarrow> nat"
axiomatization append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"
(* 
!: nth :: "'a MyList"

nth_error

length

@: append

rev
*)

axiomatization rev :: "'a List \<Rightarrow> 'a List"

lemma rev_rev_same : "rev (rev l) = l" sorry

lemma rev_app_same : "rev (append l1 l2) = append (rev l2) (rev l1)" sorry

lemma app_nil_l : "append LNil l = l" sorry

lemma app_nil_r : "append l LNil = l" sorry

lemma app_assoc : "append (append l1 l2) l3 = append l1 (append l2 l3)" sorry

lemma rev_length_same : "length (rev l) = length l" sorry

lemma app_length_same : "length (append l1 l2) = (length l1) + (length l2)" sorry

(*
lemma rev_inj: "rev l1 = rev l2 \<Longrightarrow> l1 = l2"
  apply (induction l1)
  subgoal
    apply simp
    done

  subgoal for a l1
    apply simp *)


axiomatization map_to :: "'a List \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b List"

(**r sum of array  *)
axiomatization sum_of_array :: "nat List \<Rightarrow> nat"
axiomatization fold_f :: "'a List \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b"

lemma sum_of_array_fold_same: "sum_of_array l = fold_f l (\<lambda> x y. x + y)" sorry

end