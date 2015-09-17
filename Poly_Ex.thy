theory Poly_Ex
imports "Intervals"
        "Generic_Multivariate_Polynomials"
        "~~/src/HOL/Decision_Procs/Approximation"
begin

(* Theory "Generic_Multivariate_Polynomials" contains a, more or less, 1:1 generalization
   of theory "Multivariate_Polynomial". Any additions belong here. *)

(* Conversion map for poly. *)
fun poly_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a poly \<Rightarrow> 'b poly"
where "poly_map f (poly.C c)      = poly.C (f c)"
    | "poly_map _ (poly.Bound n)  = poly.Bound n"
    | "poly_map f (poly.Add a b)  = poly.Add (poly_map f a) (poly_map f b)"
    | "poly_map f (poly.Sub a b)  = poly.Sub (poly_map f a) (poly_map f b)"
    | "poly_map f (poly.Mul a b)  = poly.Mul (poly_map f a) (poly_map f b)"
    | "poly_map f (poly.Neg a)    = poly.Neg (poly_map f a)"
    | "poly_map f (poly.Pw a n)   = poly.Pw (poly_map f a) n"
    | "poly_map f (poly.CN a n b) = poly.CN (poly_map f a) n (poly_map f b)"
    
declare [[coercion_map poly_map]]

(* Apply float interval arguments to a float poly. *)
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 6)] (poly.Add (poly.C (Float 3 5)) (poly.Bound 0))"

(* Coercing a "float poly" into a "real poly" is a homomorphism. *)
lemma poly_map_real_polyadd:
fixes p1::"float poly"
shows "poly_map real (p1 +\<^sub>p p2) = poly_map real p1 +\<^sub>p poly_map real p2"
apply(induction p1 arbitrary: p2)
apply(simp_all)[7]
proof(goals)
  case (1 x p2)
    show ?case
      by(induction p2, simp_all add: real_of_float_eq)
next
  case (2 p3 n1 p4 p2)
    show ?case
    apply(induction p2)
    using 2
    apply(simp_all add: real_of_float_eq)[7]
    proof(goals a)
      case (a p5 n2 p6)
      show ?case
      unfolding polyadd.simps(4) poly_map.simps if_distrib[of "poly_map real"]
      apply(rule if_cong)
      apply(simp_all add: 2 a, safe)
      unfolding Let_def if_distrib[of "poly_map real"]
      apply(rule if_cong)
      apply(cases "p4 +\<^sub>p p6")
      by (simp_all add: real_of_float_eq 2[symmetric])
    qed
qed
    
lemma poly_map_real_polymul:
fixes p1::"float poly"
shows "poly_map real (p1 *\<^sub>p p2) = poly_map real p1 *\<^sub>p poly_map real p2"
apply(induction p1 arbitrary: p2)
apply(simp_all)[7]
proof(goals)
  case (1 x p2)
    show ?case
      by(induction p2, simp_all add: real_of_float_eq)
next
  case (2 p3 n1 p4 p2)
    show ?case
    apply(induction p2)
    using 2
    apply(simp_all add: real_of_float_eq)[7]
    proof(goals a)
      case (a p5 n2 p6)
      show ?case
      unfolding polymul.simps(4) poly_map.simps if_distrib[of "poly_map real"]
      apply(rule if_cong)
      apply(simp)
      apply(simp add: 2)
      apply(rule if_cong)
      apply(simp)
      apply(simp add: a)
      using a
      by (simp add: poly_map_real_polyadd)
    qed
qed

(* Count the number of parameters of a polynomial. *)
fun num_params :: "'a poly \<Rightarrow> nat"
where "num_params (poly.C c) = 0"
    | "num_params (poly.Bound n)  = Suc n"
    | "num_params (poly.Add a b)  = max (num_params a) (num_params b)"
    | "num_params (poly.Sub a b)  = max (num_params a) (num_params b)"
    | "num_params (poly.Mul a b)  = max (num_params a) (num_params b)"
    | "num_params (poly.Neg a)    = num_params a"
    | "num_params (poly.Pw a n)   = num_params a"
    | "num_params (poly.CN a n b) = max (max (num_params a) (num_params b)) (Suc n)"
    
lemma [simp]: "num_params (poly_map real p) = num_params p"
by (induction p, simp_all)

(* Evaluating a float poly is equivalent to evaluating the corresponding
   real poly with the float parameters converted to reals. *)
lemma Ipoly_real_float_eqiv:
fixes p::"float poly" and xs::"float list"
assumes "num_params p \<le> length xs"
shows "Ipoly xs (p::real poly) = Ipoly xs p"
using assms by (induction p, simp_all)

lemma Ipoly_real_float_interval_eqiv:
fixes p::"float interval poly" and xs::"float interval list"
assumes "num_params p \<le> length xs"
shows "Ipoly (map (interval_map real) xs) (poly_map (interval_map real) p) = interval_map real (Ipoly xs p)"
using assms by (induction p, simp_all)


(* TODO: This lemma is a mess and similar to Ipoly_real_float_interval_eqiv. *)
lemma Ipoly_real_float_interval_eqiv':
fixes p::"float poly" and xs::"float interval list"
assumes "num_params p \<le> length xs"
shows "Ipoly (map (interval_map real) xs) (poly_map interval_of (poly_map real p)) = interval_map real (Ipoly xs (poly_map interval_of p))"
using assms by (induction p, simp_all)

(* Evaluating an "'a poly" with "'a interval" arguments is monotone. *)
lemma Ipoly_interval_args_mono:
fixes p::"'a::linordered_idom poly"
and   x::"'a list"
and   xs::"'a interval list"
assumes "x all_in xs"
assumes "num_params p \<le> length xs"
shows "Ipoly x p \<in> set_of (Ipoly xs (poly_map interval_of p))"
using assms
apply(induction p)
by (simp_all add: set_of_add_mono set_of_minus_mono set_of_mult_mono set_of_uminus_mono set_of_power_mono)

lemma Ipoly_interval_args_inc_mono:
fixes p::"'a::linordered_idom poly"
and   I::"'a interval list" and J::"'a interval list"
assumes "num_params p \<le> length I"
assumes "I all_subset J"
shows "set_of (Ipoly I (poly_map interval_of p)) \<subseteq> set_of (Ipoly J (poly_map interval_of p))"
using assms(1)
apply(induction p)
using assms(2)
by (simp_all add: set_of_add_inc set_of_sub_inc set_of_mul_inc set_of_neg_inc set_of_pow_inc)

end
