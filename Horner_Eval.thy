theory Horner_Eval
imports "Intervals"
begin

(* Function and lemmas for evaluating polynomials via the horner scheme.
   Because interval multiplication is not distributive, interval polynomials
   expressed as a sum of monomials are not equivalent to their respective horner form.
   The functions and lemmas in this theory can be used to express interval
   polynomials in horner form and prove facts about them. *)
fun horner_eval'
where "horner_eval' f x v 0 = v"
    | "horner_eval' f x v (Suc i) = horner_eval' f x (f i + x * v) i"
    
fun horner_eval
where "horner_eval f x n = horner_eval' f x 0 n"

lemmas [simp del] = horner_eval.simps

lemma horner_eval_cong:
assumes "\<And>i. i < n \<Longrightarrow> f i = g i"
assumes "x = y"
assumes "n = m"
shows "horner_eval f x n = horner_eval g y m"
proof-
  {
    fix v have "horner_eval' f x v n = horner_eval' g x v n"
      using assms(1) by (induction n arbitrary: v, simp_all)
  }
  thus ?thesis
    by (simp add: assms(2,3) horner_eval.simps)
qed
    
lemma horner_eval_eq_setsum:
fixes x::"'a::linordered_idom"
shows "horner_eval f x n = (\<Sum>i<n. f i * x^i)"
proof-
  {
    fix v have "horner_eval' f x v n = (\<Sum>i<n. f i * x^i) + v*x^n"
      by (induction n arbitrary: v, simp_all add: distrib_left mult.commute)
  }
  thus ?thesis by (simp add: horner_eval.simps)
qed

lemma horner_eval_Suc[simp]:
fixes x::"'a::linordered_idom"
shows "horner_eval f x (Suc n) = horner_eval f x n + (f n) * x^n"
unfolding horner_eval_eq_setsum
by simp

lemma horner_eval_Suc'[simp]:
fixes x::"'a::{comm_monoid_add, times}"
shows "horner_eval f x (Suc n) = f 0 + x * (horner_eval (\<lambda>i. f (Suc i)) x n)"
proof-
  {
    fix v have "horner_eval' f x v (Suc n) = f 0 + x * horner_eval' (\<lambda>i. f (Suc i)) x v n"
    by (induction n arbitrary: v, simp_all)
  }
  thus ?thesis by (simp add: horner_eval.simps)
qed

lemma horner_eval_0[simp]:
shows "horner_eval f x 0 = 0"
by (simp add: horner_eval.simps)

lemma horner_eval_interval:
fixes x::"'a::linordered_idom"
assumes "\<And>i. i < n \<Longrightarrow> f i \<in> set_of (g i)"
assumes "x \<in> set_of I"
shows "horner_eval f x n \<in> set_of (horner_eval g I n)"
proof-
  {
    fix v::'a and V::"'a interval"
    assume "v \<in> set_of V"
    hence "horner_eval' f x v n \<in> set_of (horner_eval' g I V n)"
      using assms
      apply(induction n arbitrary: v V)
      apply(simp)
      proof(goals Suc)
        case (Suc n v V)
        show ?case
          apply(simp, rule Suc(1)[OF set_of_add_mono[OF _ set_of_mult_mono]])
          using Suc(2,3,4)
          by (simp_all)
      qed
  }
  thus ?thesis by (simp add: horner_eval.simps zero_interval_def)
qed

lemma nonempty_horner_eval:
fixes I::"'a::linordered_idom interval"
assumes "nonempty I"
assumes "\<And>i. i < n \<Longrightarrow> nonempty (f i)"
shows "nonempty (horner_eval f I n)"
using assms
by (induction n arbitrary: f, simp_all add: nonempty_add zero_interval_def)

lemma horner_eval_interval_subset:
fixes I::"real interval"
assumes "nonempty I"
assumes "set_of I \<subseteq> set_of J"
assumes "\<And>i. i < n \<Longrightarrow> nonempty (f i)"
shows "set_of (horner_eval f I n) \<subseteq> set_of (horner_eval f J n)"
using assms
by (induction n arbitrary: f, simp_all add: set_of_add_inc_right set_of_mul_inc nonempty_horner_eval)

end
