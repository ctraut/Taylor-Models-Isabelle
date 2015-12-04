theory Taylor_Models_Misc
imports "~~/src/HOL/Library/Float"
        "~~/src/HOL/Library/Function_Algebras"
        "~~/src/HOL/Decision_Procs/Approximation"
        "Poly_Ex"
begin

(* This theory contains anything that doesn't belong anywhere else. *)

lemma of_nat_real_float_equiv: "(of_nat n :: real) = (of_nat n :: float)"
  by (induction n, simp_all add: of_nat_def)

lemma fact_real_float_equiv: "(fact n :: float) = (fact n :: real)"
  by (induction n) simp_all

lemma Some_those_length:
assumes "Some xs = those ys"
shows "length xs = length ys"
using assms
apply(induction ys arbitrary: xs)
apply(simp)
proof(goal_cases)
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
    proof(goal_cases)
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
    proof(goal_cases)
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

lemma fun_pow: "f^n = (\<lambda>x. (f x)^n)"
by (induction n, simp_all)

(* Count the number of parameters of a floatarith expression *)
fun num_vars :: "floatarith \<Rightarrow> nat"
where "num_vars (Add a b) = max (num_vars a) (num_vars b)"
    | "num_vars (Minus a) = num_vars a"
    | "num_vars (Mult a b) = max (num_vars a) (num_vars b)"
    | "num_vars (Inverse a) = num_vars a"
    | "num_vars (Cos a) = num_vars a"
    | "num_vars (Arctan a) = num_vars a"
    | "num_vars (Min a b) = max (num_vars a) (num_vars b)"
    | "num_vars (Max a b) = max (num_vars a) (num_vars b)"
    | "num_vars (Abs a) = num_vars a"
    | "num_vars (Sqrt a) = num_vars a"
    | "num_vars (Exp a) = num_vars a"
    | "num_vars (Ln a) = num_vars a"
    | "num_vars (Var v) = Suc v"
    | "num_vars (Power a n) = num_vars a"
    | "num_vars (Num _) = 0"
    | "num_vars Pi = 0"

(* Translate floatarith expressions by a vector of floats.*)
fun fa_translate :: "float list \<Rightarrow> floatarith \<Rightarrow> floatarith"
where "fa_translate v (Add a b) = Add (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Minus a) = Minus (fa_translate v a)"
    | "fa_translate v (Mult a b) = Mult (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Inverse a) = Inverse (fa_translate v a)"
    | "fa_translate v (Cos a) = Cos (fa_translate v a)"
    | "fa_translate v (Arctan a) = Arctan (fa_translate v a)"
    | "fa_translate v (Min a b) = Min (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Max a b) = Max (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Abs a) = Abs (fa_translate v a)"
    | "fa_translate v (Sqrt a) = Sqrt (fa_translate v a)"
    | "fa_translate v (Exp a) = Exp (fa_translate v a)"
    | "fa_translate v (Ln a) = Ln (fa_translate v a)"
    | "fa_translate v (Var n) = Add (Var n) (Num (v!n))"
    | "fa_translate v (Power a n) = Power (fa_translate v a) n"
    | "fa_translate v (Num c) = Num c"
    | "fa_translate v Pi = Pi"

lemma fa_translate_correct:
assumes "num_vars f \<le> length I"
assumes "length v = length I"
shows "interpret_floatarith (fa_translate v f) I = interpret_floatarith f (list_op op+ I v)"
using assms
by (induction f, simp_all)

end
