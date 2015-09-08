theory Taylor_Models_Misc
imports "~~/src/HOL/Library/Float"
begin

(* This theory contains anything that doesn't belong anywhere else. *)

lemma of_nat_real_float_equiv: "(of_nat n :: real) = (of_nat n :: float)"
  by (induction n, simp_all add: of_nat_def)

lemma fact_real_float_equiv: "(fact n :: float) = (fact n :: real)"
  by (induction n, simp_all add: of_nat_real_float_equiv)

lemma Some_those_length:
assumes "Some xs = those ys"
shows "length xs = length ys"
using assms
apply(induction ys arbitrary: xs)
apply(simp)
proof(goals)
  case (1 a ys xs)
  show ?case
    apply(cases a)
    using 1(2)
    apply(simp)
    proof-
      fix a' assume a_def: "a = Some a'"
      from 1(2)
      have "Some xs = map_option (op # a') (those ys)"
        by (simp add: a_def)
      thus "length xs = length (a # ys)"
        using 1(1) by (metis (no_types, lifting) length_Cons map_option_eq_Some)
    qed
qed

lemma Some_those_nth:
assumes "Some xs = those ys"
assumes "i < length xs"
shows "Some (xs!i) = ys!i"
proof-
  have "None \<in> set ys \<Longrightarrow> those ys = None"
    apply(induction ys)
    apply(simp)
    proof(goals)
      case (1 a ys) thus ?case by (cases a, simp_all)
    qed
  hence "None \<notin> set ys"
    using assms(1) by auto
  then obtain y where y_def: "Some y = ys!i"
    by (metis Some_those_length assms not_None_eq nth_mem)
  hence "xs!i = y"
    using assms
    apply(induction i arbitrary: y xs ys)
    apply(simp_all)
    proof(goals)
      case (1 y xs ys)
      thus ?case
      apply(cases ys)
      apply(simp_all)
      by (metis nth_Cons_0 option.distinct(1) option.map_disc_iff option.map_sel option.sel option.simps(5))
    next
      case (2 i y xs ys)
      thus ?case
      apply(cases ys)
      apply(simp_all)
      by (smt Suc_less_eq length_Cons map_option_eq_Some nth_Cons_Suc option.case_eq_if option.distinct(1))
    qed
  thus ?thesis
    by (simp add: y_def)
qed

end
