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

value "LCons (3::nat) LNil"
(** how to represent an array [1;2;3] using List ?

step1: [3]


step2: LCons 1 (LCons 2 (LCons (3::nat) LNil))

step3:

 *)

value "LCons 1 (LCons 2 (LCons (3::nat) LNil))"


value "hd ([1,2,3]::nat list)"
(*
value "hd ([]::nat list)" *)


(**
datatype 'a option =
    None
  | Some (the: 'a)

struct succ_or_fail ={
  is_ok: _Bool;
  res: int;
}

definition my_system:: "... \<Rightarrow> 'a option" where

Safety Property:
lemma my_system_is_safe "pre_condition \<Longrightarrow> my_system ... \<noteq> None"
*)

(**r https://coq.inria.fr/doc/v8.9/stdlib/Coq.Lists.List.html#hd_error  *)
fun hd_error :: "'a List \<Rightarrow> 'a option" where
"hd_error LNil = None" |
"hd_error (LCons h t) = Some h"
term "None"
term "Some"

datatype 'a option3 =
Bad |
EFlag int |
Normal (the: 'a)


datatype 'a option4 =
Bad1 |
EFlag1 int |
Normal1 (the: 'a) |
Return

definition hd_error_1 :: "'a List \<Rightarrow> 'a option" where
"hd_error_1 l =(
  case l of
  LNil \<Rightarrow> None |
  LCons h t \<Rightarrow> Some h
)"

lemma hd_error_def_same: "hd_error l = hd_error_1 l"
  apply (unfold hd_error_1_def)
  apply (cases l)
\<comment>\<open>  prefer 2 \<close>
  subgoal
\<comment>\<open> left   = hd_error LNil = None
    right  = (case LNil of LNil \<Rightarrow> None | LCons h t \<Rightarrow> Some h) = None
 \<close>
    apply simp
    done

  subgoal for myhead mytail 
\<comment>\<open> left   = hd_error (LCons myhead mytail) = Some myhead
    right  = (case (LCons myhead mytail) of LNil \<Rightarrow> None | LCons h t \<Rightarrow> Some h)
           = Some myhead
 \<close>
    apply simp
    done 
  done


value "hd_error ((LCons 1 (LCons 2 (LCons 3 LNil)))::nat List)"
value "hd_error (LNil::nat List)"

lemma hd_error_is_safe: "l \<noteq> LNil \<Longrightarrow> hd_error l \<noteq> None"
  apply (cases "l")
  subgoal
    apply simp
    done

  subgoal for myhead mytail
    apply simp
    done
  done

definition hd_default :: "'a List \<Rightarrow> 'a \<Rightarrow> 'a" where
"hd_default l default_v = (
  case l of
  LNil \<Rightarrow> default_v |
  LCons h d \<Rightarrow> h
)"

lemma hd_error_hd_default_some:
  "hd_error l = Some v \<Longrightarrow> hd_default l d_v = v"
  apply (cases l)
  subgoal
    apply simp
    done

  subgoal for x1 x2
\<comment> \<open>
hd_error l = Some v \<Longrightarrow> l = LCons x1 x2 \<Longrightarrow> hd_default l d_v = v \<close>
    apply simp

\<comment> \<open>
hd_error l = Some v and l = LCons x1 x2

step1 ( rewrite using l_eq): hd_error (LCons x1 x2) = Some v

step2 (definition of hd_error):  Some x1 = Some v

step2 (definition of hd_error):  x1 = v

x1 = v


x1 = v \<Longrightarrow> l = LCons x1 x2 \<Longrightarrow> hd_default l d_v = v \<close>
    apply (unfold hd_default_def)
    apply simp
    done
  done

lemma hd_error_hd_default_none: 
"hd_error l = None \<Longrightarrow> hd_default l d_v = d_v"
  apply (cases l)
  subgoal
    apply simp
    apply (unfold hd_default_def)
    apply simp
    done

  subgoal for x1 x2
\<comment> \<open>
hd_error l = None \<Longrightarrow> l = LCons x1 x2 \<Longrightarrow> hd_default l d_v = d_v

hd_error l = None and l = LCons x1 x2
step1 ( rewrite using l_eq): hd_error (LCons x1 x2) = None

step2 (definition of hd_error):  Some x1 = None

Some x1 = None iff False

Some x1 = None \<Longrightarrow> hd_default l d_v = d_v
 \<close>
    apply simp
    done
  done

value "last ([1,2,3]::nat list)"
(*
value "last ([]::nat list)"
fun last_error :: "'a list \<Rightarrow> 'a option" where
definition last_error1 :: "'a list \<Rightarrow> 'a list option" where *)

axiomatization last_error   :: "'a List \<Rightarrow> 'a option"
axiomatization last_error1  :: "'a list \<Rightarrow> 'a list option"


value "[1,2,(3::nat)]!0" (*
value "[1,2,(3::nat)]!3" *)
fun nth_error :: "'a List \<Rightarrow> nat \<Rightarrow> 'a option" where
"nth_error l n = (
  case l of
  LNil \<Rightarrow> None |
  LCons h d \<Rightarrow> (
    case n of
    0 \<Rightarrow> Some h |
    Suc k \<Rightarrow> nth_error d k
  )
)"

(**r [10]  *)
value "nth_error (LCons (10::nat) LNil) 1"

fun length :: "'a List \<Rightarrow> nat" where
"length l = (
  case l of
  LNil \<Rightarrow> 0 |
  LCons h d \<Rightarrow> 1 + (length d)
)"

value "length (LCons 100 (LCons (10::nat) LNil))"
(**
length (LCons 100 (LCons (10::nat) LNil)) =

1 + (length (LCons (10::nat) LNil))

1 + 1 + (length LNil)

1 + 1 + 0

1 + 1

2
*)

fun length_1 :: "'a List \<Rightarrow> nat \<Rightarrow> nat" where
"length_1 l v = (
  case l of
  LNil \<Rightarrow> v |
  LCons h d \<Rightarrow> length_1 d (v+1)
)"

definition length2 :: "'a List \<Rightarrow> nat" where
"length2 l = length_1 l 0"

(*
lemma lenght2_plus: "length_1 l v = v + (length_1 l 0)"
  apply (induct l)
  subgoal
    apply simp
    done

  subgoal for x1 l
    apply simp

lemma length_eq : "length l = length2 l"
  apply (unfold length2_def)
  apply (induct l)
  subgoal
    apply simp
    done

  subgoal for x1 l
    apply simp
    apply (cases l)
    subgoal
      apply simp
      done
    subgoal for x2 l2

*)

value "length_1 (LCons (10::nat) LNil) 0"

fun append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
"append l1 l2 = (
  case l1 of
  LNil \<Rightarrow> l2 |
  LCons h d \<Rightarrow> LCons h (append d l2)
)"

value "append (LCons (10::nat) (LCons 20 LNil)) (LCons (100::nat) (LCons 200 LNil))"
(* [10, 20] ++ [100, 200] = [10, 20, 100, 200] 
!: nth :: "'a MyList"

a[n]

nth_error

length

@: append

rev
*)

(**

LCons 10 (LCons 20 (LCons 100 (LCons 200 LNil)))

'a \<Rightarrow> 'b \<Rightarrow> 'c 

'a \<Rightarrow> ('b * 'c)

append l1 l2 = l1 ++ l2
*)

fun rev :: "'a List \<Rightarrow> 'a List" where
"rev l = (
  case l of
  LNil \<Rightarrow> LNil |
  LCons h d \<Rightarrow> append (rev d) (LCons h LNil)
)"
value "rev (LCons 10 (LCons 20 (LCons 100 (LCons (200::nat) LNil))))"
(**r
  rev (LCons 10 (LCons 20 (LCons 100 (LCons (200::nat) LNil))))
= append (rev (LCons 20 (LCons 100 (LCons (200::nat) LNil)))) (LCons 10 LNil)
= ...    (append (rev (LCons 100 (LCons (200::nat) LNil)) (LCons 20 LNil))  ...
= ...    ...     (append (rev (LCons (200::nat) LNil) (LCons 100 LNil)))  ... ...
= ...    ...     ...     (append (rev LNil) (LCons 200 LNil)) ...  ... ...
= ...    ...     ...     ...     (append LNil (LCons 200 LNil)) ... ...  ... ...
= ...    ...     ...     \<dots>      (LCons 200 LNil) ... ...  ... ...

--- append  (LCons 200 LNil) (LCons 100 LNil)
=   (LCons 200 LCons 100 LNil)  ... ...

--- append  (LCons 200 LCons 100 LNil) (LCons 20 LNil)

*)

lemma app_nil_l : "append LNil l = l" sorry

lemma app_nil_r : "append l LNil = l" sorry

lemma app_assoc : "append (append l1 l2) l3 = append l1 (append l2 l3)" sorry

lemma rev_length_same : "length (rev l) = length l" sorry

lemma app_length_same : "length (append l1 l2) = (length l1) + (length l2)" sorry


lemma rev_rev_same : "rev (rev l) = l" sorry

lemma rev_app_same : "rev (append l1 l2) = append (rev l2) (rev l1)" sorry

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