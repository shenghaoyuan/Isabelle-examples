theory MyLogic
  imports
    Main
begin

section \<open> Introduction Rules \<close>

(**r lemma conjI: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q"  *)
lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  apply (rule HOL.conjI)
  subgoal
    apply assumption
    done
  subgoal
    apply assumption
    done
  done

(**r lemma disjI1: "P \<Longrightarrow> P \<or> Q" *)
lemma "A \<Longrightarrow> A \<or> B"
  apply (rule HOL.disjI1)
  apply assumption
  done


section \<open> Elimination Rules \<close>
lemma "A \<Longrightarrow> A \<or> B"
  apply (erule HOL.disjI1)
  done

(**r

lemma disjE:
  assumes major: "P \<or> Q"
    and minorP: "P \<Longrightarrow> R"
    and minorQ: "Q \<Longrightarrow> R"
  shows R

lemma disjI2: "Q \<Longrightarrow> P \<or> Q"
*)
lemma "B \<or> A \<Longrightarrow> A \<or> B"
  apply (erule HOL.disjE)
  subgoal by (erule HOL.disjI2)  
  subgoal by (erule HOL.disjI1)
  done

(**r
impI: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q"
mp: "\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q"

lemma impE:
  assumes "P \<longrightarrow> Q" P "Q \<Longrightarrow> R"
  shows R
*)
lemma "(A \<longrightarrow> B) \<Longrightarrow> (B \<longrightarrow> C) \<Longrightarrow> (A \<longrightarrow> C)"
  apply (rule impI)
\<comment> \<open> A \<longrightarrow> B \<Longrightarrow> B \<longrightarrow> C \<Longrightarrow> A \<Longrightarrow> C  \<close>
  apply (erule mp) \<comment> \<open> i.e. apply (erule mp [of B C]) where P = B and Q = C, why not `apply (erule mp [of A B])` because the goal is C \<close>
\<comment> \<open> A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B  \<close>
  apply (erule mp)
  apply assumption
  done

section \<open> Destruction Rules \<close>
lemma "B \<or> A \<Longrightarrow> A \<or> B"
  apply (drule HOL.disjE [of _ _ "A\<or>B"])
    prefer 3
  subgoal by assumption
  subgoal by (erule HOL.disjI2)  
  subgoal by (erule HOL.disjI1)
  done


section \<open> Substitution \<close>
(**r 

lemma imp_conv_disj: "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P) \<or> Q"

lemma de_Morgan_disj: "\<not> (P \<or> Q) \<longleftrightarrow> \<not> P \<and> \<not> Q"

lemma excluded_middle: "\<not> P \<or> P"

lemma simp_thms:
  shows not_not: "(\<not> \<not> P) = P"
*)
lemma "((A \<longrightarrow> B)\<longrightarrow> A) \<longrightarrow> A"
  apply (subst imp_conv_disj)
  apply (subst imp_conv_disj)
  apply (subst de_Morgan_disj)
  apply (subst not_not)
  apply (rule impI)
  apply (erule HOL.disjE)
  subgoal
    apply (erule HOL.conjE)
    apply assumption
    done
  subgoal by assumption
  done
end