theory MyNat
  imports
    Main
begin

datatype mynat =
  MyZero | \<comment>\<open> 0 is a natural number \<close>
  MySuc (n: mynat) \<comment>\<open> if n is a natural number, then n+1 is a natural number \<close>

datatype myZ =
Zzero |
ZPos (z: myZ) |
ZNeg (z: myZ)

value "0::nat"
(**r 5 = S (S (S (S (S O))))
0 = O
1 = S O
*)
(**r why can we do `Mathematical Induction`? *)

value MySuc 
(** MySuc is a function: "mynat \<Rightarrow> mynat" *)

value "MySuc MyZero"
(** "MySuc MyZero" is 1 *)

value MyZero 
(** MyZero is a function: "mynat" *)

(**r each definition in Isabelle/HOL is a function *)
end