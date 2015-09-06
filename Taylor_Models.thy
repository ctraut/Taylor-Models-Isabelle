theory Taylor_Models
imports "Intervals"
        "Generic_Multivariate_Polynomials"
        "~~/src/HOL/Decision_Procs/Approximation"
        "~~/src/HOL/Library/Function_Algebras"
        "~~/src/HOL/Library/Set_Algebras"
begin

(* Trying out arithmetic on intervals and polynomials with interval coefficients. *)
value "Ivl (-1::float) 1 + Ivl 0 1"
value "Ivl (-8::float) 2 + Ivl (-2) (-1)"
value "Ivl (0::real) 1 * Ivl 0 1"
value "Ivl (-10::real) 6 * Ivl (-4) 2"
value "Ivl (-1::real) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 * Ivl 0 1"
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 (-6))] (poly.Add (poly.C (Ivl (Float 3 (-5)) (Float 3 (-5)))) (poly.Bound 0))"

(* Computing interval bounds on arithmetic expressions. 
   TODO: - For now, I hard-code the precision, because I don't want to carry it around.
           Later, it will become explicit. *)
definition prec::nat where "prec=64"
fun compute_bound :: "floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_bound p I = (case approx prec p (map (\<lambda>i. case i of Ivl a b \<Rightarrow> Some (a, b)) I) of Some (a, b) \<Rightarrow> (if a \<le> b then Some (Ivl a b) else None) | _ \<Rightarrow> None)"

value "compute_bound (Add (Var 0) (Num 3)) [Ivl 1 2]"

lemma valid_ivl_compute_bound:
assumes "Some i = compute_bound f I"
shows "valid_ivl i"
proof-
  obtain l u where i_decomp: "i = Ivl l u" using interval.exhaust by auto
  from assms
  show ?thesis
    apply(simp add: i_decomp)
    by (smt interval.inject less_eq_float.rep_eq option.case_eq_if option.distinct(1) option.sel prod.case_eq_if)
qed

lemma compute_bound_correct:
fixes i::"real list"
assumes "Some ivl = compute_bound f I"
assumes "\<And>n. n < length I \<Longrightarrow> i!n \<in> set_of (interval_map real (I!n))"
assumes "length I = length i"
shows "interpret_floatarith f i \<in> set_of (interval_map real ivl)"
proof-
  have "\<forall>n < length I. \<exists>a b. I!n = Ivl a b"
    proof(safe)
      fix n assume "n < length I"
      obtain a b where ab_def: "I!n = Ivl a b"
        using interval.exhaust by auto
      show "\<exists>a b. I ! n = Ivl a b"
        by ((rule exI)+, rule ab_def)
    qed
  then obtain fa fb where I_def': "\<And>n. n < length I \<Longrightarrow> I!n = Ivl (fa n) (fb n)"
    by (auto simp: choice_iff')
    
  def a\<equiv>"map (\<lambda>x. fa (nat x)) ([0..<length I])"
  def b\<equiv>"map (\<lambda>x. fb (nat x)) ([0..<length I])"
  
  have length_a: "length a = length I"
    by (simp add: a_def)
  have length_b: "length b = length I"
    by (simp add: b_def)
    
  have I_a_b: "\<And>n. n < length I \<Longrightarrow> I!n = Ivl (a!n) (b!n)"
    by (simp add: I_def' a_def b_def)
  have I_def: "I = map (\<lambda>(a, b). Ivl a b) (zip a b)"
    unfolding list_all2_eq list_all2_conv_all_nth
    proof-
      have "map snd (zip a b) = b"
        by (simp add: length_a length_b)
      hence "length (zip a b) = length I"
        by (metis (full_types) length_b length_map)
      thus "length I = length (map (\<lambda>(x, y). Ivl x y) (zip a b)) \<and> (\<forall>n<length I. I ! n = map (\<lambda>(x, y). Ivl x y) (zip a b) ! n)"
        by (simp add: I_a_b)
    qed
    
  obtain l u where ivl_def: "ivl = Ivl l u" using interval.exhaust by auto
    
  have "bounded_by i (map Some (zip a b))"
    proof(simp add: bounded_by_def length_a length_b, safe)
      fix n assume "n < length I"
      from assms(2)[OF this]
      have concl: "i ! n \<in> {(a!n)..(b!n)}"           
        using `n < length I` by (auto simp: I_def set_of_def)
      
      show "(a ! n) \<le> i ! n"
        using concl by simp
      show "i ! n \<le> real (b ! n)"
        using concl by simp
    qed
  moreover have "Some (l, u) = approx prec f (map Some (zip a b))"
    proof(rule ccontr)
      assume contr_assm: "Some (l, u) \<noteq> approx prec f (map Some (zip a b))"
      have [simp]: "map (case_interval (\<lambda>a b. Some (a, b)) \<circ> (\<lambda>(x, y). Ivl x y)) (zip a b) = map Some (zip a b)"
        by auto
      show False
        proof(cases "approx prec f (map Some (zip a b))")
          assume "approx prec f (map Some (zip a b)) = None"
          from assms(1)[unfolded compute_bound.simps I_def, simplified, unfolded this]
          show "False"
            by auto
        next
          fix ab' assume assm: "approx prec f (map Some (zip a b)) = Some ab'"
          obtain a' b' where ab'_def: "ab' = (a', b')"
            using old.prod.exhaust by blast
          from assms(1)[unfolded compute_bound.simps I_def, simplified, unfolded assm this, simplified]
          show False using contr_assm assm by (cases "real a' \<le> real b'", simp_all add: ab'_def ivl_def)
        qed
    qed
  ultimately show ?thesis
    using approx by (auto simp: ivl_def)
qed

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
    
(* Coercions on intervals. *)

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

lemma valid_ivl_Ipoly:
fixes A :: "'a::linordered_idom interval list"
fixes p :: "'a poly"
assumes "num_params p \<le> length I"
assumes "\<And>n. n < length I \<Longrightarrow> valid_ivl (I!n)"
shows "valid_ivl (Ipoly I (poly_map interval_of p))"
using assms
by (induction p, simp_all add: valid_ivl_add valid_ivl_sub valid_ivl_neg valid_ivl_pow)

(* Evaluating an "'a poly" with "'a interval" arguments is monotone. *)
lemma Ipoly_interval_args_mono:
fixes p::"'a::linordered_idom poly"
and   x::"'a list"
and   xs::"'a interval list"
assumes "length x = length xs"
assumes "num_params p \<le> length xs"
assumes "\<And>n. n < length xs \<Longrightarrow> x!n \<in> set_of (xs!n)"
shows "Ipoly x p \<in> set_of (Ipoly xs (poly_map interval_of p))"
using assms
apply(induction p)
by (simp_all add: set_of_add_mono set_of_minus_mono set_of_mult_mono set_of_uminus_mono set_of_power_mono)

(* Taylor models are a pair of a polynomial and an absolute error bound (an interval). *)
datatype taylor_model = TaylorModel "float poly" "float interval"

primrec ivl_tm :: "taylor_model \<Rightarrow> float interval"
where "ivl_tm (TaylorModel _ i) = i"

primrec poly_tm :: "taylor_model \<Rightarrow> float poly"
where "poly_tm (TaylorModel p _) = p"

(* A taylor model is valid, if its polynomial has the right number of parameters and it is close to f on I.  *)
primrec valid_tm :: "float interval list \<Rightarrow> (real list \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> bool"
where "valid_tm I f (TaylorModel p i) = (valid_ivl i \<and> num_params p \<le> length I \<and> (\<forall>x. length x = length I \<and> (\<forall>n<length I. x!n \<in> set_of (I!n)) \<longrightarrow> (f x - Ipoly x (p::real poly) \<in> set_of i)))"

lemma valid_tmD[elim]:
assumes "valid_tm I f t"
obtains p l u
where "t = TaylorModel p (Ivl l u)"
and   "valid_ivl (Ivl l u)"
and   "num_params p \<le> length I"
and   "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)) \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}"
proof-
  from assms obtain p i where t_def: "t = TaylorModel p i"
    using taylor_model.exhaust by auto
  obtain l u where i_def: "i = Ivl l u"
    using interval.exhaust by auto
      
  show ?thesis
    apply(rule, simp add: t_def(1) i_def)
    using assms by (auto simp: t_def i_def)
qed

lemma valid_tmD':
assumes "valid_tm I f t"
obtains p i
where "t = TaylorModel p i"
and   "valid_ivl i"
and   "num_params p \<le> length I"
and   "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)) \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> set_of i"
using assms by auto

lemma valid_tmI[intro]:
assumes "t = TaylorModel p (Ivl l u)"
and   "valid_ivl (Ivl l u)"
and   "num_params p \<le> length I"
and   "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)) \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}"
shows "valid_tm I f t"
using assms by (auto simp: valid_tm_def)

lemma valid_tmI':
assumes "t = TaylorModel p i"
and   "valid_ivl i"
and   "num_params p \<le> length I"
and   "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)) \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> set_of i"
shows "valid_tm I f t"
using assms by (auto simp: valid_tm_def)

(* Bound a polynomial by simply evaluating it with interval arguments. *)
fun compute_bound_tm :: "taylor_model \<Rightarrow> float interval list \<Rightarrow> float interval"
where "compute_bound_tm (TaylorModel p i) Is = Ipoly Is p + i"

lemma compute_bound_tm_correct:
fixes S :: "real set list"
fixes I :: "float interval list"
fixes x :: "real list"
fixes f :: "real list \<Rightarrow> real"
assumes "valid_tm I f t"
assumes "\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)"
assumes "length x = length I"
shows "f x \<in> set_of (compute_bound_tm t I)"
proof-
  obtain p l u where t_def: "t = TaylorModel p (Ivl l u)"
    by (metis interval.exhaust taylor_model.exhaust)
    
  from assms
  have valid:
    "num_params p \<le> length I"
    "f x - Ipoly x p \<in> set_of (Ivl l u)"
      by (auto simp: t_def)
     
  have a1: "Ipoly x (poly_map real p) \<in> set_of (Ipoly (map (interval_map real) I) (poly_map interval_of (poly_map real p)))"
    by (rule Ipoly_interval_args_mono, simp_all add: assms valid(1))
    
  have a2: "poly_map interval_of (poly_map real p) = poly_map (interval_map real) (poly_map interval_of p)"
    by (induction p, simp_all)
  
  show "f x \<in> set_of (compute_bound_tm t I)"
    unfolding t_def compute_bound_tm.simps
    using set_of_add_mono[OF a1 valid(2), unfolded a2, simplified]
    apply(rule subst[where P="\<lambda>I. f x \<in> set_of I", rotated])
    apply(subst Ipoly_real_float_interval_eqiv)
    apply(rule xt1(4)[OF valid(1)])
    by (induction p, simp_all)
qed

(* Operations on taylor models. *)
fun TMNeg :: "taylor_model \<Rightarrow> taylor_model"
where "TMNeg (TaylorModel p i) = TaylorModel (poly.Neg p) (-i)"

fun TMAdd :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMAdd (TaylorModel p1 i1) (TaylorModel p2 i2) = TaylorModel (poly.Add p1 p2) (i1+i2)"

fun TMSub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMSub t1 t2 = TMAdd t1 (TMNeg t2)"

(* TODO: Currently, this increases the degree of the polynomial! *)
fun TMMul :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> float interval list \<Rightarrow> taylor_model"
where "TMMul (TaylorModel p1 i1) (TaylorModel p2 i2) I = (
  let d1=Ipoly I p1;
      d2=Ipoly I p2
  in TaylorModel (poly.Mul p1 p2) (i1*d2 + d1*i2 + i1*i2))"

(* Validity of is preserved under taylor model arithmetic. *)
lemma TMNeg_valid:
assumes "valid_tm I f t"
shows "valid_tm I (-f) (TMNeg t)"
proof-
  from valid_tmD[OF assms]
  obtain p l u where t_def: 
    "t = TaylorModel p (Ivl l u)"
    "valid_ivl (Ivl l u)"
    "num_params p \<le> length I"
    "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n))) \<Longrightarrow> f x - Ipoly x p \<in> {l..u}"
      by blast
  show ?thesis
    apply(rule)
    apply(simp add: t_def(1) uminus_interval_def)
    using t_def(2)
    apply(simp)
    apply(simp add: t_def(3))
    proof-
      fix x assume assms: "length x = length I" "(\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n)))"
      show "(-f) x - Ipoly x (Neg p) \<in> {(-u)..(-l)}"
        using t_def(4)[OF assms] by simp
    qed
qed

lemma TMAdd_valid:
assumes "valid_tm I f t1"
assumes "valid_tm I g t2"
shows "valid_tm I (f + g) (TMAdd t1 t2)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 l1 u1 where t1_def:
    "t1 = TaylorModel p1 (Ivl l1 u1)"
    "valid_ivl (Ivl l1 u1)"
    "num_params p1 \<le> length I"
    "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n))) \<Longrightarrow> f x - Ipoly x p1 \<in> {l1..u1}"
      by blast
  from valid_tmD[OF assms(2)]
  obtain p2 l2 u2 where t2_def:
    "t2 = TaylorModel p2 (Ivl l2 u2)"
    "valid_ivl (Ivl l2 u2)"
    "num_params p2 \<le> length I"
    "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n))) \<Longrightarrow> g x - Ipoly x p2 \<in> {l2..u2}"
      by blast
   
  show "valid_tm I (f + g) (TMAdd t1 t2)"
    proof(rule)
      show "num_params (poly.Add p1 p2) \<le> length I"
      by (simp add: t1_def(3) t2_def(3))
    next
      fix x assume assms: "length x = length I" "(\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n)))"
      from t1_def(4)[OF this] t2_def(4)[OF this]
       show "(f + g) x - Ipoly x (poly.Add p1 p2) \<in> {(l1+l2)..(u1+u2)}"
        by simp
    next
      show "valid_ivl (Ivl (l1 + l2) (u1 + u2))"
        using t1_def(2) t2_def(2)
        by simp
    qed (simp add: t1_def(1) t2_def(1) plus_interval_def)
qed

lemma TMSub_valid:
assumes "valid_tm I f t1"
assumes "valid_tm I g t2"
shows "valid_tm I (f - g) (TMSub t1 t2)"
using TMAdd_valid[OF assms(1) TMNeg_valid[OF assms(2)]]
by simp

(* TODO: Clean this proof up! *)
lemma TMMul_valid:
assumes "valid_tm I f t1"
assumes "valid_tm I g t2"
assumes "\<And>n. n < length I \<Longrightarrow> valid_ivl (I ! n)"
shows "valid_tm I (f * g) (TMMul t1 t2 I)"
proof-
  from valid_tmD'[OF assms(1)]
  obtain p1 i1 where t1_def:
    "t1 = TaylorModel p1 i1"
    "valid_ivl i1"
    "num_params p1 \<le> length I"
    "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n))) \<Longrightarrow> f x - Ipoly x p1 \<in> set_of i1"
      by blast
  from valid_tmD'[OF assms(2)]
  obtain p2 i2 where t2_def:
    "t2 = TaylorModel p2 i2"
    "valid_ivl i2"
    "num_params p2 \<le> length I"
    "\<And>x. length x = length I \<Longrightarrow> (\<And>n. n < length I \<Longrightarrow> x ! n \<in> set_of (interval_map real (I ! n))) \<Longrightarrow> g x - Ipoly x p2 \<in> set_of i2"
      by blast
        
  have v1: "valid_ivl (Ipoly I (poly_map interval_of p1))"
    by (rule valid_ivl_Ipoly[OF t1_def(3) assms(3)])
  have v2: "valid_ivl (Ipoly I (poly_map interval_of p2))"
    by (rule valid_ivl_Ipoly[OF t2_def(3) assms(3)])
      
  show "valid_tm I (f * g) (TMMul t1 t2 I)"
    unfolding t1_def t2_def TMMul.simps Let_def
    apply(rule valid_tmI')
    unfolding taylor_model.inject
    apply(rule conjI[OF refl refl])
    defer
    using t1_def(3) t2_def(3)
    apply(simp)
    proof(goals)
      case (1 x)
      
      obtain d1 :: real where d1_def: "d1 \<in> set_of i1" "f x - Ipoly x p1 = d1"
        using t1_def(4)[OF 1] by auto
      obtain d2 :: real where d2_def: "d2 \<in> set_of i2" "g x - Ipoly x p2 = d2"
        using t2_def(4)[OF 1] by auto
        
      have a1: "length x = length (map (interval_map real) I)"
        using 1(1) by simp
      have a2: "num_params (poly_map real p1) \<le> length (map (interval_map real) I)"
        using t1_def(3) by simp
      have a2': "num_params (poly_map real p2) \<le> length (map (interval_map real) I)"
        using t2_def(3) by simp
      have a3: "\<And>n. n < length (map (interval_map real) I) \<Longrightarrow> x ! n \<in> set_of (map (interval_map real) I ! n)"
        using 1(2) by simp
        
      have b1: "Ipoly x p1 \<in> set_of (Ipoly I (poly_map interval_of p1))"
        using Ipoly_interval_args_mono[OF a1 a2 a3] t1_def(3)
        by (simp add: Ipoly_real_float_interval_eqiv')
      have b2: "Ipoly x p2 \<in> set_of (Ipoly I (poly_map interval_of p2))"
        using Ipoly_interval_args_mono[OF a1 a2' a3] t2_def(3)
        by (simp add: Ipoly_real_float_interval_eqiv')
      
      have "(f * g) x = f x * g x"
        by auto
      also have "... = (d1 + Ipoly x p1) * (d2 + Ipoly x p2)"
        by (simp add: d1_def(2)[symmetric] d2_def(2)[symmetric])
      also have "... = Ipoly x p1 * Ipoly x p2 + d1 * Ipoly x p2 + Ipoly x p1 * d2 + d1 * d2"
        by (simp add: algebra_simps)
      finally have f_times_g_eq: "(f * g) x - Ipoly x p1 * Ipoly x p2 = d1 * Ipoly x p2 + Ipoly x p1 * d2 + d1 * d2"
        by simp
      also have "... \<in> set_of (interval_map real (i1 * Ipoly I (poly_map interval_of p2))) +  set_of (interval_map real (Ipoly I (poly_map interval_of p1) * i2)) + set_of (i1 * i2)"
        apply(rule set_plus_intro[OF set_plus_intro])
        using d1_def(1) d2_def(1) b1 b2
        by (simp_all add: set_of_mult_mono)
      also have "... = set_of (interval_map real (i1 * Ipoly I (poly_map interval_of p2) + Ipoly I (poly_map interval_of p1) * i2 + i1 * i2))"
        by (simp add: v1 v2 t1_def(2) t2_def(2) set_of_add_distrib valid_ivl_add)
      finally have "(f * g) x - Ipoly x p1 * Ipoly x p2  \<in> set_of (interval_map real (i1 * Ipoly I (poly_map interval_of p2) + Ipoly I (poly_map interval_of p1) * i2 + i1 * i2))"
        .

      thus ?case
      by simp
    next
      case 2
      show ?case
        using t1_def(2) t2_def(2) v1 v2
        by (simp add: valid_ivl_add)
    qed
qed

(* Taylor models for basic functions. *)

(* Compute the nth derivative of a floatarith expression *)
fun deriv :: "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
where "deriv v f 0 = f"
    | "deriv v f (Suc n) = DERIV_floatarith 0 (deriv v f n)"

lemma isDERIV_DERIV_floatarith:
assumes "isDERIV n f vs"
shows "isDERIV n (DERIV_floatarith n f) vs"
using assms
apply(induction f)
apply(simp_all add: numeral_eq_Suc add_nonneg_eq_0_iff)
proof-
  fix f m assume hyp: "isDERIV n f vs \<Longrightarrow> isDERIV n (DERIV_floatarith n f) vs"
  show "isDERIV n (Power f m) vs \<Longrightarrow> isDERIV n (DERIV_floatarith n (Power f m)) vs"
    apply(cases m)
    apply(simp_all)
    using hyp
    by (metis isDERIV.simps(14) isDERIV.simps(15) polypow.cases)
qed

lemma deriv_correct:
assumes "isDERIV 0 f [t]"
shows "((\<lambda>x. interpret_floatarith (deriv 0 f n) [x]) has_real_derivative interpret_floatarith (deriv 0 f (Suc n)) [t]) (at t)"
apply(simp)
apply(rule DERIV_floatarith[where n=0 and vs="[undefined]", simplified])
apply(induction n)
using isDERIV_DERIV_floatarith assms
by auto

(* Function and leamms for evaluating a polynomial via the horner scheme. *)
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

lemma valid_ivl_horner_eval:
fixes I::"'a::linordered_idom interval"
assumes "valid_ivl I"
assumes "\<And>i. i < n \<Longrightarrow> valid_ivl (f i)"
shows "valid_ivl (horner_eval f I n)"
using assms
by (induction n arbitrary: f, simp_all add: valid_ivl_add zero_interval_def)

(* TODO: Do I need this lemma? *)
lemma horner_eval_interval_subset:
fixes I::"real interval"
assumes "valid_ivl I"
assumes "set_of I \<subseteq> set_of J"
assumes "\<And>i. i < n \<Longrightarrow> valid_ivl (f i)"
shows "set_of (horner_eval f I n) \<subseteq> set_of (horner_eval f J n)"
using assms
apply(induction n arbitrary: f)
apply(simp)
apply(simp)
apply(rule set_of_add_inc_right)
apply(rule valid_ivl_mul)
apply(rule set_of_mul_inc)
by (simp_all add: valid_ivl_horner_eval)

(* Compute a taylor model from an arbitrary, univariate floatarith expression, if possible. *)

(* The interval coefficients of the taylor polynom,
   i.e. the real coefficients approximated by a float interval. *)
fun TMf_c :: "nat \<Rightarrow> float interval \<Rightarrow> floatarith \<Rightarrow> float interval option"
where "TMf_c n i f = compute_bound (Mult (deriv 0 f n) (Inverse (Num (fact n)))) [i]"

(* Make a list of the n coefficients. *) 
fun TMf_cs' :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> float interval option list"
where "TMf_cs' 0 I a f = []"
    | "TMf_cs' (Suc n) I a f = (TMf_c n (interval_of a) f) # (TMf_cs' n I a f)"

(* Also add the n+1-th coefficient, representing the error contribution, and reorder the list. *)
fun TMf_cs :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> float interval list option"
where "TMf_cs n I a f = those (rev (TMf_c n I f # (TMf_cs' n I a f)))"

value "the (TMf_cs 5 (Ivl 0 2) 1 (Cos (Var 0)))" 

(* TODO: Is this necessary? *)
lemma of_nat_real_float_equiv: "(of_nat n :: real) = (of_nat n :: float)"
  by (induction n, simp_all add: of_nat_def)

lemma fact_real_float_equiv: "(fact n :: float) = (fact n :: real)"
  by (induction n, simp_all add: of_nat_real_float_equiv)

lemma TMf_c_correct:
fixes A::"float interval" and I::"float interval" and f::floatarith and a::real
assumes "a \<in> set_of A"
assumes "Some I = TMf_c i A f"
shows "valid_ivl I"
and   "interpret_floatarith (deriv 0 f i) [a] / fact i \<in> set_of I"
proof-
  obtain l u where I_decomp: "I = Ivl l u" using interval.exhaust by auto

  show result: "interpret_floatarith (deriv 0 f i) [a] / fact i \<in> set_of (interval_map real I)"
    using compute_bound_correct[OF assms(2)[unfolded TMf_c.simps], where i="[a]"] assms(1)
    by (simp add: divide_real_def fact_real_float_equiv)
  hence "set_of (interval_map real I) \<noteq> {}"
    by auto
  thus "valid_ivl I"
    by (simp add: I_decomp)
qed

lemma Some_those_length:
assumes "Some xs = those ys"
shows   "length xs = length ys"
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

lemma TMf_cs_length:
assumes "Some cs = TMf_cs n A a f"
shows "length cs = n + 1"
apply(simp add: Some_those_length[OF assms[unfolded TMf_cs.simps]])
by (induction n, simp_all)

lemma TMf_cs_correct:
fixes A::"float interval" and f::floatarith
assumes "a \<in> set_of A"
assumes "Some cs = TMf_cs n A a f"
shows "\<And>i. i < n \<Longrightarrow> Some (cs!i) = TMf_c i (interval_of a) f"
and   "Some (cs!n) = TMf_c n A f"
proof-
  from TMf_cs_length[OF assms(2)]
  have n_ineq: "n < length cs"
    by simp
  from TMf_cs_length[OF assms(2)] assms(2)
  have total_length: "length (TMf_c n A f # TMf_cs' n A a f) = Suc n"
    by (metis Some_those_length Suc_eq_plus1 TMf_cs.simps length_rev)
    
  from Some_those_nth[OF assms(2)[unfolded TMf_cs.simps] n_ineq]
  show "Some (cs ! n) = TMf_c n A f"
    apply(subst (asm) rev_nth)
    using total_length by auto
next
  fix i assume "i < n"
  from TMf_cs_length[OF assms(2)] this
  have i_ineq: "i < length cs"
    by simp

  from TMf_cs_length[OF assms(2)] assms(2)
  have total_length: "length (TMf_c n A f # TMf_cs' n A a f) = Suc n"
    by (metis Some_those_length Suc_eq_plus1 TMf_cs.simps length_rev)
    
  have "Some (cs ! i) = (TMf_c n A f # TMf_cs' n A a f) ! (n - i)"
    using Some_those_nth[OF assms(2)[unfolded TMf_cs.simps] i_ineq]
    apply(subst (asm) rev_nth)
    using total_length `i < n`
    by auto
  also have "... = (TMf_cs' n A a f) ! (n - Suc i)"
    using `i < n` by simp
  also have "...  = TMf_c i (interval_of a) f"
    using `i < n` by (induction n, auto simp: less_Suc_eq)
  finally show "Some (cs ! i) = TMf_c i (interval_of a) f" .
qed

lemma TMf_cs_valid:
fixes A::"float interval" and f::floatarith
assumes "a \<in> set_of A"
assumes "Some cs = TMf_cs n A a f"
shows "\<And>i. i \<le> n \<Longrightarrow> valid_ivl (cs!i)"
using TMf_c_correct(1)[OF _ TMf_cs_correct(1)[OF assms], where a=a, simplified] 
      TMf_c_correct(1)[OF _ TMf_cs_correct(2)[OF assms], where a=a, simplified, OF assms(1)]
by (auto simp: nat_less_le)


abbreviation "x_minus_a\<equiv>\<lambda>a. poly.Sub (poly.Bound 0) (poly.C a)"

fun TMfloatarith' :: "float \<Rightarrow> float interval list \<Rightarrow> float poly \<times> float interval poly"
where "TMfloatarith' a [] = (poly.C 0, poly.C 0)"
    | "TMfloatarith' a (c # cs) = (\<lambda>(pf, pi). (poly.Add (poly.C (mid c)) (poly.Mul (x_minus_a a) pf), poly.Add (poly.C (centered c)) (poly.Mul (x_minus_a (interval_of a)) pi))) (TMfloatarith' a cs)"
    
fun TMfloatarith :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "TMfloatarith n I a f = map_option (\<lambda>(pf, pi). TaylorModel pf (Ipoly [I] pi)) (map_option (TMfloatarith' a) (TMf_cs n I a f))"

value "TMfloatarith 5 (Ivl (-1) 1) 0 (Cos (Var 0))"
value "interval_map real (compute_bound_tm (the (TMfloatarith 5 (Ivl (-1) 1) 0 (Cos (Var 0)))) [Ivl (-1) 1])"

lemma TMfloatarith_valid:
assumes "0 < n"
assumes "a \<in> set_of I"
assumes "\<And>x. x \<in> set_of I \<Longrightarrow> isDERIV 0 f [x]"
assumes "Some t = TMfloatarith n I a f"
shows "valid_tm [I] (interpret_floatarith f) t"
proof-
  from assms(4)[unfolded TMfloatarith.simps]
  obtain pf pi where Some_pf_pi_def: "Some (pf, pi) = map_option (TMfloatarith' a) (TMf_cs n I a f)"
    by (metis (no_types, lifting) map_option_eq_Some prod.collapse)
  then have t_def: "t = TaylorModel pf (Ipoly [I] pi)"
    using assms(4)[unfolded TMfloatarith.simps]
    by (metis old.prod.case option.sel option.simps(9))
  from Some_pf_pi_def obtain cs where cs_def: "Some cs = TMf_cs n I a f"
    by (metis map_option_eq_Some)
  have pfpi_def: "(pf, pi) = TMfloatarith' a cs"
    by (metis Some_pf_pi_def cs_def map_option_eq_Some option.sel)
  from TMf_cs_valid[OF assms(2) cs_def] TMf_cs_length[OF cs_def]
  have valid_cs: "\<And>i. i < length cs \<Longrightarrow> valid_ivl (cs ! i)"
    by auto
  
  show ?thesis
  proof(rule valid_tmI')
    show "t = TaylorModel pf (Ipoly [I] pi)"
      by (simp add: t_def)
  next
    show "valid_ivl (Ipoly [I] pi)"
      using pfpi_def valid_cs
      apply(induction cs arbitrary: pf pi)
      apply(simp add: zero_interval_def)
      proof-
        case (Cons c cs pf pi)
        then obtain pf' pi' where pf'pi'_def: "(pf', pi') = TMfloatarith' a cs"
          using prod.collapse by blast
        from this Cons(2)[simplified]
        have pi_decomp: "pi = poly.Add (c - Ivl (mid c) (mid c))\<^sub>p (Mul (x_minus_a (Ivl a a)) pi')"
          by (metis old.prod.case prod.sel(2))
        show ?case
          by (simp add: pi_decomp Cons(3)[of 0, simplified] valid_ivl_sub valid_ivl_add)
      qed
  next
    show "num_params pf \<le> length [I]"
      using pfpi_def
      apply(induction cs arbitrary: pf pi)
      apply(simp)
      proof-
        case (Cons c cs pf pi)
        then obtain pf' pi' where pf'pi'_def: "(pf', pi') = TMfloatarith' a cs"
          using prod.collapse by blast
        from this Cons(2)[simplified]
        have pf_decomp: "pf = poly.Add (mid c)\<^sub>p (Mul (x_minus_a a) pf')"
          by (metis old.prod.case prod.sel(1))
        show ?case
          using Cons(1)[OF pf'pi'_def]
          by (simp add: pf_decomp)
      qed
  next
    fix xs assume hyps: " length xs = length [I]" "\<And>n. n < length [I] \<Longrightarrow> xs ! n \<in> set_of (interval_map real ([I] ! n))"
    from hyps(1) obtain x where xs_def: "xs = [x]" by (auto simp: length_Suc_conv)
    hence x_def: "x \<in> set_of I" using hyps(2) by simp
    
    show "interpret_floatarith f xs - Ipoly xs (poly_map real pf) \<in> set_of (Ipoly [I] pi)"
    proof(cases "x = a")
      case True
      have pf_val_at_a: "Ipoly [real a] (poly_map real pf) = mid (cs ! 0)"
        using pfpi_def TMf_cs_length[OF cs_def]
        apply(induction cs arbitrary: pf pi n)
        apply(simp)
        proof-
          case (Cons c cs pf pi n)
          then obtain pf' pi' where pf'pi'_def: "(pf', pi') = TMfloatarith' a cs"
            using prod.collapse by blast
          from this Cons(2)[simplified]
          have pf_decomp: "pf = poly.Add (mid c)\<^sub>p (Mul (x_minus_a a) pf')"
            by (metis old.prod.case prod.sel(1))
          show ?case
            using Cons(1)[OF pf'pi'_def]
            by (simp add: pf_decomp)
        qed
      from TMf_c_correct(2)[OF _ TMf_cs_correct(1)[OF assms(2) cs_def assms(1)], of a]
      have "interpret_floatarith f xs \<in> set_of (interval_map real (cs ! 0))"
        by (simp add: xs_def `x = a`)
      have "interpret_floatarith f xs - Ipoly xs (poly_map real pf) \<in> set_of (interval_map real (cs ! 0) - (mid (cs ! 0)))"
        using pf_val_at_a TMf_c_correct(2)[OF _ TMf_cs_correct(1)[OF assms(2) cs_def assms(1)], of a]
        by (simp add: xs_def `x = a` set_of_minus_mono)
      also have "... \<subseteq>  set_of (interval_map real (Ipoly [I] pi))"
        proof-
          from TMf_cs_length[OF cs_def]
          obtain c cs' where cs_decomp: "cs = c # cs'" 
            by (metis Suc_eq_plus1 list.size(3) neq_Nil_conv old.nat.distinct(2))
          obtain pi' where pi_decomp: "pi = poly.Add (c - interval_of (mid c))\<^sub>p (Mul (x_minus_a (interval_of a)) pi')"
            using pfpi_def
            by (simp add: cs_decomp case_prod_beta)
            
          show ?thesis
            apply(simp add: cs_decomp pi_decomp)
            apply(rule set_of_add_inc[where B=0, simplified])
            using valid_cs[of 0] TMf_cs_length[OF cs_def]
            apply(simp add: valid_ivl_sub cs_decomp)
            apply(simp add: zero_interval_def)
            apply(simp)
            apply(simp add: zero_interval_def)
            apply(rule set_of_mul_contains_zero)
            apply(rule disjI1)
            by (simp add: assms(2) set_of_minus_mono[where a="real a" and b="real a", simplified])
        qed
      finally show ?thesis .
    next
      case False
      
      obtain l u where I_def: "I = Ivl l u" by (metis interval.exhaust) 
      
      have "\<exists>t. (if x < real a then x < t \<and> t < real a else real a < t \<and> t < x) \<and>
                interpret_floatarith f [x] =
                  (\<Sum>m<n. interpret_floatarith (deriv 0 f m) [real a] / fact m * (x - real a) ^ m)
                  + interpret_floatarith (deriv 0 f n) [t] / fact n * (x - real a) ^ n"
        apply(rule taylor[where a=l and b=u])
        apply(rule `0 < n`)
        apply(simp)
        apply(safe)[1]
        apply(rule deriv_correct[OF assms(3)])
        apply(simp add: I_def)
        using assms(2) x_def `x \<noteq> a`
        by (simp_all add: I_def)
      then obtain t 
      where "if x < real a then x < t \<and> t < real a else real a < t \<and> t < x"
      and taylor_expansion:
        "interpret_floatarith f [x] = 
           (\<Sum>m<n. interpret_floatarith (deriv 0 f m) [real a] / fact m * (x - real a) ^ m)
           + interpret_floatarith (deriv 0 f n) [t] / fact n * (x - real a) ^ n"
        by auto
      from this(1) have t_in_I: "t \<in> set_of I"
        using assms(2) x_def
        apply(simp add: I_def)
        by (meson less_eq_real_def order_trans)
      
      from pfpi_def TMf_cs_length[OF cs_def]
      have Ipoly_pf_eq: "Ipoly xs pf = (\<Sum>m<Suc n. mid (cs!m) * (x - a) ^ m)"
        apply(induction cs arbitrary: n pf pi)
        apply(simp add: xs_def)
        proof-
          case (Cons c cs n pf pi)
          obtain pf' pi' where pf'pi'_def: "(pf', pi') = TMfloatarith' a cs"
            using prod.collapse by blast
          from Cons(2)
          have pf_def: "pf = poly.Add (mid c)\<^sub>p (Mul (x_minus_a a) pf')"
          and  pi_def: "pi = poly.Add (c - interval_of (mid c))\<^sub>p (Mul (x_minus_a (interval_of a)) pi')"
            by (auto simp: pf'pi'_def[symmetric])
          from Cons(3) have [simp]: "length cs = n" by simp
            
          show ?case
            apply(cases cs)
            using Cons(2,3)
            apply(simp)
            proof-
              fix c' cs' assume cs_def: "cs = c' # cs'"
              
              have "Ipoly xs (poly_map real pf) = real (mid c) + (x - real a) * Ipoly [x] (poly_map real pf')"
                by (simp add: pf_def xs_def)
              also have "... = real (mid c) + (x - real a) * (\<Sum>m<Suc (length cs'). real (mid (cs ! m)) * (x - real a) ^ m)"
                using Cons(1)[OF pf'pi'_def, where n="length cs'"]
                by (simp add: cs_def xs_def)
              also have "... = real (mid c) + (x - real a) * (\<Sum>m<length cs. real (mid ((c # cs) ! Suc m)) * (x - real a) ^ m)"
                by (simp add: cs_def)
              also have "... = real (mid c) + (\<Sum>m<n. real (mid ((c # cs) ! Suc m)) * (x - real a) ^ Suc m)"
                by (simp add:  setsum_right_distrib linordered_field_class.sign_simps(25))
              also have "... = real (mid c) + (\<Sum>m\<in>{1..n}. real (mid ((c # cs) ! m)) * (x - real a) ^ m)"
                apply(subst setsum_shift_bounds_Suc_ivl[symmetric, of _ 0 "n", unfolded atLeast0LessThan])
                unfolding atLeastLessThanSuc_atLeastAtMost
                by simp
              also have "... = (\<Sum>m\<in>{0..n}. real (mid ((c # cs) ! m)) * (x - real a) ^ m)"
                using setsum_add_nat_ivl[where m=0 and n=1 and p="Suc n" and f="\<lambda>m. real (mid ((c # cs) ! m)) * (x - real a) ^ m", unfolded atLeastLessThanSuc_atLeastAtMost, simplified]
                by simp
              finally show "Ipoly xs (poly_map real pf) = (\<Sum>m<Suc n. real (mid ((c # cs) ! m)) * (x - real a) ^ m)"
                unfolding atLeast0AtMost lessThan_Suc_atMost
                by simp
            qed
        qed
      
      def cr\<equiv>"\<lambda>i. if i < n then (interpret_floatarith (deriv 0 f i) [real a] / fact i - real (mid (cs ! i)))
                           else (interpret_floatarith (deriv 0 f i) [t] / fact n - real (mid (cs ! i)))"
      def ci\<equiv>"\<lambda>i. (interval_map real (cs ! i) - interval_of (real (mid (cs ! i))))"
      
      have "(\<Sum>m<n. interpret_floatarith (deriv 0 f m) [real a] / fact m * (x - real a) ^ m)
                 + interpret_floatarith (deriv 0 f n) [t] / fact n * (x - real a) ^ n
                 - Ipoly xs (poly_map real pf)
                 = (\<Sum>m<n. cr m  * (x - real a) ^ m) + cr n * (x - real a) ^ n"
        by (simp add: Ipoly_pf_eq algebra_simps setsum.distrib[symmetric] cr_def)
      also have "... = horner_eval cr (x - real a) (Suc n)"
        by (simp add: horner_eval_eq_setsum)
      also have "... \<in> set_of (horner_eval ci (x - real a) (Suc n))"
        apply(rule horner_eval_interval)
        apply(simp add: cr_def ci_def)
        apply(safe)[1]
        using TMf_c_correct(2)[OF _ TMf_cs_correct(1)[OF  assms(2) cs_def], where a=a, simplified]
        apply(simp)
        apply(rule set_of_minus_mono)
        using TMf_c_correct(2)[OF t_in_I TMf_cs_correct(2)[OF assms(2) cs_def]]
        apply(simp_all)
        proof(goals)
          case(1 i)
          hence "i = n" by simp
          thus ?case
            apply(simp)
            apply(rule set_of_minus_mono[OF 1(3)])
            by simp
        qed
      also have "... \<subseteq> set_of (interval_map real (Ipoly [I] pi))"
        using ci_def pfpi_def TMf_cs_length[OF cs_def] valid_cs
        proof(induction n arbitrary: cs pi pf ci)
          case (0 cs pi pf)
          from 0(2) obtain c where cs_def: "cs = [c]"
            by (metis Suc_eq_plus1 Suc_length_conv length_0_conv)
          from 0(1) have pi_def: "pi = poly.Add (centered c)\<^sub>p (Mul (x_minus_a (Ivl a a)) (0)\<^sub>p)"
            by (simp add: cs_def)
          show ?case
            by (simp add: 0(1) cs_def pi_def)
        next
          case(Suc n cs pi)
          from Suc(3) obtain c cs' where cs_def: "cs = c # cs'" 
                                   and length_cs': "length cs' = n + 1"
            by (metis Suc_eq_plus1 length_Suc_conv)
          hence "cs' \<noteq> []" by auto
          from cs_def obtain pf' pi' where pf'pi'_def: "(pf', pi') = TMfloatarith' a cs'"
            using prod.collapse by blast
          from Suc(2) have pi_def: "pi = poly.Add (centered c)\<^sub>p (Mul (x_minus_a (Ivl a a)) pi')"
            by (simp add: cs_def pf'pi'_def[symmetric])
            
          have "set_of (horner_eval (\<lambda>i. interval_map real (cs ! i) - interval_of (real (mid (cs ! i)))) (interval_of (x - real a)) (Suc (Suc n)))
              = set_of (interval_map real (c) - interval_of (real (mid c))
                        + interval_of (x - real a) * horner_eval (\<lambda>i. interval_map real (cs' !  i) - interval_of (real (mid (cs' ! i)))) (interval_of (x - real a)) (Suc n))"
            by (simp add: cs_def)
          also have "... \<subseteq> set_of (interval_map real (c) - interval_of (real (mid c)) + interval_of (x - real a) * interval_map real (Ipoly [I] pi'))"
            apply(rule set_of_add_inc_right)
            apply(rule valid_ivl_mul)
            apply(rule set_of_mul_inc_right)
            prefer 2
            apply(rule Suc(1)[OF pf'pi'_def length_cs'])
            using Suc(4)[unfolded cs_def] length_cs'
            apply (metis Suc.prems(2) Suc_eq_plus1 Suc_less_eq2 cs_def nth_Cons_Suc)
            using Suc(4)[unfolded cs_def, of 1, simplified, OF `cs' \<noteq> []`]
            by (simp add: valid_ivl_add valid_ivl_sub)
          also have "... \<subseteq> set_of (interval_map real (Ipoly [I] pi))"
            apply(simp add: pi_def)
            apply(rule set_of_add_inc_right)
            apply(rule valid_ivl_mul)
            apply(rule set_of_mul_inc_left)
            by (simp_all add: set_of_minus_mono[OF x_def])
          finally show ?case .
        qed
      finally show ?thesis
        using taylor_expansion
        by (simp add: xs_def)
    qed
  qed
qed

(* TODO: Derive taylor models for sin by translating the cosine. *)
definition Sin::"floatarith \<Rightarrow> floatarith"
where "Sin a = Minus (Cos (Add (Mult Pi (Num (Float 1 (- 1)))) (Minus a)))"

(* Compute taylor models of degree n from floatarith expressions.
   TODO: For now, this returns an option. This will change as soon as 
         all of floatarith can be converted to a taylor model. *)
fun compute_taylor_model :: "nat \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "compute_taylor_model _ I (Num c) = Some (TaylorModel (poly.C c) (Ivl 0 0))"
    | "compute_taylor_model _ I (Var n) = Some (TaylorModel (poly.Bound n) (Ivl 0 0))"
    | "compute_taylor_model n I (Add a b) = (
         case (compute_taylor_model n I a, compute_taylor_model n I b) 
         of (Some t1, Some t2) \<Rightarrow> Some (TMAdd t1 t2) | _ \<Rightarrow> None)"
    | "compute_taylor_model n I (Minus a) = (
         case compute_taylor_model n I a of Some t1 \<Rightarrow> Some (TMNeg t1) | _ \<Rightarrow> None)"
    | "compute_taylor_model n I _ = None"

lemma computed_taylor_model_valid:
assumes "num_vars f \<le> length I"
assumes "Some t = compute_taylor_model n I f"
shows "valid_tm I (interpret_floatarith f) t"
using assms
proof(induct f arbitrary: t)
case (Add a b t)
  obtain t1 where t1_def: "Some t1 = compute_taylor_model n I a"
    by (metis (no_types, lifting) Add(4) compute_taylor_model.simps(3) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "Some t2 = compute_taylor_model n I b"
    by (smt Add(4) compute_taylor_model.simps(3) option.case_eq_if option.collapse prod.case)
  have t_def: "t = TMAdd t1 t2"
    using Add(4) t1_def t2_def
    by (metis compute_taylor_model.simps(3) option.case(2) option.inject prod.case)
  
  have [simp]: "interpret_floatarith (floatarith.Add a b) = interpret_floatarith a + interpret_floatarith b"
    by auto
  show "valid_tm I (interpret_floatarith (floatarith.Add a b)) t"
    apply(simp add: t_def)
    apply(rule TMAdd_valid[OF Add(1)[OF _ t1_def] Add(2)[OF _ t2_def]])
    using Add(3) by auto
next
case (Minus a t)
   have [simp]: "interpret_floatarith (Minus a) = -interpret_floatarith a"
     by auto
   
   obtain t1 where t1_def: "Some t1 = compute_taylor_model n I a"
     by (metis Minus(3) compute_taylor_model.simps(4) option.collapse option.simps(4))
   have t_def: "t = TMNeg t1"
     by (metis Minus(3) compute_taylor_model.simps(4) option.case(2) option.inject t1_def)
     
   show "valid_tm I (interpret_floatarith (Minus a)) t"
     apply(simp add: t_def, rule TMNeg_valid[OF Minus(1)[OF _ t1_def]])
     using Minus(2) by auto
qed (simp_all add: valid_tm_def)

(* Compute some taylor models. *)
value "the (compute_taylor_model 10 [Ivl 0 1] (Num 2))"
value "the (compute_taylor_model 10 [Ivl 0 1] (Var 0))"
value "the (compute_taylor_model 10 [Ivl 0 1, Ivl 0 1] (Add (Var 0) (Var 1)))"

(* Automatically find interval bounds for floatarith expressions. *)
fun compute_ivl_bound :: "nat \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> float interval option"
where "compute_ivl_bound n I f = (case compute_taylor_model n I f of None \<Rightarrow> None | Some t \<Rightarrow> Some (compute_bound_tm t I))"

(* Automatically computed bounds are correct. *)
lemma compute_ivl_bound_correct:
assumes "num_vars f \<le> length I"
assumes "Some B = compute_ivl_bound n I f"
assumes "\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)"
assumes "length x = length I"
shows "interpret_floatarith f x \<in> set_of B"
proof-
  (* Since we have a bound B, there must have been a taylor model used to compute it. *)
  from assms(2) obtain t where B_def: "B = compute_bound_tm t I" 
                           and t_def: "Some t = compute_taylor_model n I f"
    by (simp, metis (mono_tags, lifting) option.case_eq_if option.collapse option.distinct(1) option.inject)
  from compute_bound_tm_correct[OF computed_taylor_model_valid[OF assms(1) t_def] assms(3,4)]
  show ?thesis
    by (simp add: B_def)
qed

(* Compute bounds on some expressions. *)
value "the (compute_ivl_bound 10 [Ivl (-2) 1, Ivl 9 11] (Add (Var 0) (Var 1)))"

lemma
shows "8 \<in> set_of (the (compute_ivl_bound 10 [Ivl (-2) 1, Ivl 9 11] (Add (Var 0) (Var 1))))" 
(is "?v \<in> set_of ?B")
proof-
  have "?B = Ivl 7 12"
  apply(simp add: plus_interval_def eq_onp_same_args minus_float.abs_eq)
  by (metis add_One_commute float_of_numeral one_plus_numeral one_plus_numeral semiring_norm(3) semiring_norm(4))
  thus ?thesis by simp
qed


end