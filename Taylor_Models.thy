theory Taylor_Models
imports "Generic_Multivariate_Polynomials"
        "~~/src/HOL/Decision_Procs/Approximation"
        "~~/src/HOL/Library/Function_Algebras"
        "~~/src/HOL/Library/Set_Algebras"
        (*"/home/christoph/Documents/Studium/Interdisziplinäres Projekt/afp-linode/thys/Affine_Arithmetic/Affine_Arithmetic"*)
begin

(* I define my own interval type here. TODO: Do I really need to do this? *)
datatype 'a interval = Ivl 'a 'a

definition lower :: "'a interval \<Rightarrow> 'a"
where "lower i = (case i of (Ivl l u) \<Rightarrow> l)"

definition upper :: "'a interval \<Rightarrow> 'a"
where "upper i = (case i of (Ivl l u) \<Rightarrow> u)"

definition set_of :: "('a::ord) interval \<Rightarrow> 'a set"
where "set_of i = (case i of (Ivl l u) \<Rightarrow> {l..u})"

definition prod_of :: "('a::ord) interval \<Rightarrow> 'a \<times> 'a"
where "prod_of i = (case i of (Ivl l u) \<Rightarrow> (l, u))"

lemmas [simp] = lower_def upper_def set_of_def prod_of_def


(* Type instantiations for intervals. *)
instantiation "interval" :: (plus) plus
begin
  definition "a + b = Ivl (lower a + lower b) (upper a + upper b)"
  instance ..
end

instantiation "interval" :: (zero) zero
begin
  definition "0 = Ivl 0 0"
  instance ..
end

instantiation "interval" :: ("{times, ord}") times
begin
definition "a * b = Ivl (min (min (lower a * lower b) (upper a * lower b)) 
                             (min (lower a * upper b) (upper a * upper b)))
                        (max (max (lower a * lower b) (upper a * lower b)) 
                             (max (lower a * upper b) (upper a * upper b)))"
instance ..

end

instantiation "interval" :: (one) one
begin
  definition "1 = Ivl 1 1"
  instance ..
end

instantiation "interval" :: ("{inverse, ord}") inverse
begin
  definition "inverse a = Ivl (min (inverse (lower a)) (inverse (upper a))) (max (inverse (lower a)) (inverse (upper a)))"
  instance ..
end

lemmas [simp] = plus_interval_def times_interval_def

value "Ivl (0::real) 1 * Ivl 0 1"
value "Ivl (-1::real) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 * Ivl 0 1"

lemma ivl_add_correct:
fixes x::real (* TODO: Relax! *)
assumes "x \<in> {a..b}"
assumes "y \<in> {c..d}"
shows "x + y \<in> set_of (Ivl a b + Ivl c d)"
using assms by simp

lemma ivl_mul_correct:
fixes x::real (* TODO: Relax! *)
assumes "x \<in> {a..b}"
assumes "y \<in> {c..d}"
shows "x * y \<in> set_of (Ivl a b * Ivl c d)"
using assms
by (simp, smt mult.commute mult_right_less_imp_less mult_right_mono_neg)

(* TODO: - For now, I hard-code the precision, because I don't want to carry it around.
           Later, it will become explicit. *)
fun compute_bound :: "floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_bound p I = (case approx 64 p (map (\<lambda>i. case i of Ivl a b \<Rightarrow> Some (a, b)) I) of Some (a, b) \<Rightarrow> Some (Ivl a b) | _ \<Rightarrow> None)"

value "compute_bound (Add (Var 0) (Num 3)) [Ivl 1 2]"

lemma compute_bound_correct:
assumes "Some (Ivl l u) = compute_bound f I"
assumes "\<And>n. n < length I \<Longrightarrow> i!n \<in> set_of (I!n)"
assumes "length I \<le> length i" (* TODO: Do I need this assumption? *)
shows "interpret_floatarith f i \<in> {l..u}"
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
    
  have "bounded_by i (map Some (zip a b))"
    proof(simp add: bounded_by_def length_a length_b, safe)
      fix n assume "n < length I"
      from assms(2)[OF this]
      have "i ! n \<in> {(a!n)..(b!n)}"           
        using `n < length I` by (auto simp: I_def)
      moreover have "map real i ! n = real (i ! n)"
        apply(rule List.nth_map)
        using `n < length I` `length I \<le> length i`
        by simp
      ultimately have concl: "map real i ! n \<in> {(a!n)..(b!n)}"
        by auto
      
      show "(a ! n) \<le> map real i ! n"
        using concl by simp
      show "map real i ! n \<le> real (b ! n)"
        using concl by simp
    qed
  moreover have "Some (l, u) = approx 64 f (map Some (zip a b))"
    proof(rule ccontr)
      assume contr_assm: "Some (l, u) \<noteq> approx 64 f (map Some (zip a b))"
      have [simp]: "map (case_interval (\<lambda>a b. Some (a, b)) \<circ> (\<lambda>(x, y). Ivl x y)) (zip a b) = map Some (zip a b)"
        by auto
      show False
        proof(cases "approx 64 f (map Some (zip a b))")
          assume "approx 64 f (map Some (zip a b)) = None"
          from assms(1)[unfolded compute_bound.simps I_def, simplified, unfolded this]
          show "False"
            by auto
        next
          fix ab' assume assm: "approx 64 f (map Some (zip a b)) = Some ab'"
          obtain a' b' where ab'_def: "ab' = (a', b')"
            using old.prod.exhaust by blast
          from assms(1)[unfolded compute_bound.simps I_def, simplified, unfolded assm this, simplified]
          show False using contr_assm assm by (simp add: ab'_def)
        qed
    qed
  ultimately show ?thesis
    using approx by auto
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

declare [[coercion_map poly_map]]

(* Count the number of parameters of a polynom. *)
fun num_params :: "'a poly \<Rightarrow> nat"
where "num_params (poly.C c) = 0"
    | "num_params (poly.Bound n)  = Suc n"
    | "num_params (poly.Add a b)  = max (num_params a) (num_params b)"
    | "num_params (poly.Sub a b)  = max (num_params a) (num_params b)"
    | "num_params (poly.Mul a b)  = max (num_params a) (num_params b)"
    | "num_params (poly.Neg a)    = num_params a"
    | "num_params (poly.Pw a n)   = num_params a"
    | "num_params (poly.CN a n b) = max (max (num_params a) (num_params b)) (Suc n)"

(* Evaluating a float poly is equivalent to evaluating the corresponding
   real poly with the corresponding real parameters. *)
lemma Ipoly_real_float_eqiv:
fixes p::"float poly" and xs::"float list" and r::float
assumes "num_params p \<le> length xs"
shows "Ipoly xs (p::real poly) = Ipoly xs p"
using assms by (induct p, simp_all)


(* Taylor models are a pair of a polynomial and an absolute error bound (an interval). *)
datatype taylor_model = TaylorModel "float poly" "float interval"

(* TODO: Implement! Try to translate a float poly into an floatarith expression and use compute_bound. 
         Use the fact, that compute_bound can never return None when called on a polygon. *)
fun compute_bound_TM :: "taylor_model \<Rightarrow> float interval list \<Rightarrow> float interval"
where "compute_bound_TM _ _ = undefined"

(* TODO: Can I simplify my notion of validity? *)
definition valid_tm :: "real set list \<Rightarrow> (real list \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> bool"
where "valid_tm S f t = (\<forall>x. length x = length S \<and> (\<forall>n<length S. x!n \<in> S!n) \<longrightarrow> (case t of (TaylorModel p (Ivl l u)) \<Rightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}))"

lemma valid_tmD[elim]:
assumes "valid_tm S f t"
obtains p l u
where "t = TaylorModel p (Ivl l u)"
and   "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x!n \<in> S!n) \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}"
proof-
  from assms obtain p i where t_def: "t = TaylorModel p i"
    using taylor_model.exhaust by auto
  obtain l u where i_def: "i = Ivl l u"
    using interval.exhaust by auto
      
  show ?thesis
    apply(rule, simp add: t_def(1) i_def)
    using assms
    by (simp add: valid_tm_def t_def i_def)
qed

lemma valid_tmI[intro]:
assumes "t = TaylorModel p (Ivl l u)"
and   "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x!n \<in> S!n) \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}"
shows "valid_tm S f t"
using assms by (auto simp: valid_tm_def)

(* Operations on taylor models. *)
fun TMNeg :: "taylor_model \<Rightarrow> taylor_model"
where "TMNeg (TaylorModel p (Ivl l u)) = TaylorModel (poly.Neg p) (Ivl (-u) (-l))"

fun TMAdd :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMAdd (TaylorModel p1 i1) (TaylorModel p2 i2) = TaylorModel (poly.Add p1 p2) (i1+i2)"

fun TMSub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMSub t1 t2 = TMAdd t1 (TMNeg t2)"

(* TODO: - Implement correctly. 
         - Make sure this never increases the degree of the polynomial! *)
fun TMMul :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> float interval \<Rightarrow> taylor_model"
where "TMMul (TaylorModel p1 i1) (TaylorModel p2 i2) I = TaylorModel (poly.Mul p1 p2) (i1*i2)"

(* Validity of taylor models is preserved under these operations. *)
lemma TMNeg_valid:
assumes "valid_tm S f t"
shows "valid_tm S (-f) (TMNeg t)"
proof-
  from valid_tmD[OF assms]
  obtain p l u where t_def: 
    "t = TaylorModel p (Ivl l u)"
    "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n) \<Longrightarrow> f x - Ipoly x p \<in> {l..u}"
      by blast
  show ?thesis
    apply(rule)
    apply(simp add: t_def(1))
    proof-
      fix x assume assms: "length x = length S" "(\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n)"
      show "(-f) x - Ipoly x (Neg p) \<in> {(-u)..(-l)}"
        using t_def(2)[OF assms] by simp
    qed
qed

lemma TMAdd_valid:
assumes "valid_tm S f t1"
assumes "valid_tm S g t2"
shows "valid_tm S (f + g) (TMAdd t1 t2)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 l1 u1 where t1_def: "t1 = TaylorModel p1 (Ivl l1 u1)" "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n) \<Longrightarrow> f x - Ipoly x p1 \<in> {l1..u1}"
    by blast
  from valid_tmD[OF assms(2)]
  obtain p2 l2 u2 where t2_def: "t2 = TaylorModel p2 (Ivl l2 u2)" "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n) \<Longrightarrow> g x - Ipoly x p2 \<in> {l2..u2}"
    by blast
  show "valid_tm S (f + g) (TMAdd t1 t2)"
    proof(rule, simp add: t1_def(1) t2_def(1))
      fix x assume assms: "length x = length S" "(\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n)"
      from t1_def(2)[OF this] t2_def(2)[OF this]
       show "(f + g) x - Ipoly x (poly.Add p1 p2) \<in> {(l1+l2)..(u1+u2)}"
        by simp
    qed
qed

lemma TMSub_valid:
assumes "valid_tm S f t1"
assumes "valid_tm S g t2"
shows "valid_tm S (f - g) (TMSub t1 t2)"
using TMAdd_valid[OF assms(1) TMNeg_valid[OF assms(2)]]
by simp

(* Multiplication is done by approximating the domain with a float interval. 
   TODO: Prove as soon as the definition of TMMul is finished. *)
lemma TMMul_valid:
assumes "valid_tm S f t1"
assumes "valid_tm S g t2"
shows "valid_tm S (f * g) (TMMul t1 t2 I)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 l1 u1 where t1_def: "t1 = TaylorModel p1 (Ivl l1 u1)" "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n) \<Longrightarrow> f x - Ipoly x p1 \<in> {l1..u1}"
    by blast
  from valid_tmD[OF assms(2)]
  obtain p2 l2 u2 where t2_def: "t2 = TaylorModel p2 (Ivl l2 u2)" "\<And>x. length x = length S \<Longrightarrow> (\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n) \<Longrightarrow> g x - Ipoly x p2 \<in> {l2..u2}"
    by blast
    
  {
    fix x assume assms: "length x = length S" "(\<And>n. n < length S \<Longrightarrow> x ! n \<in> S ! n)"
    
    obtain d1 :: real where d1_def: "d1 \<in> {l1..u1}" "f x - Ipoly x p1 = d1"
      using t1_def(2)[OF assms] by auto
    obtain d2 :: real where d2_def: " d2 \<in> {l2..u2}" "g x - Ipoly x p2 = d2"
      using t2_def(2)[OF assms] by auto
    
    have "(f * g) x = f x * g x"
      by auto
    also have "... = (d1 + Ipoly x p1) * (d2 + Ipoly x p2)"
      by (simp add: d1_def(2)[symmetric] d2_def(2)[symmetric])
    also have "... = Ipoly x p1 * Ipoly x p2 + d1 * Ipoly x p2 + Ipoly x p1 * d2 + d1 * d2"
      (is "_ = ?a + ?b d1 + ?c d2 + ?d  d1 d2")
      by (simp add: algebra_simps)
    finally have f_times_g_eq: "(f * g) x = ?a + ?b d1 + ?c d2 + ?d  d1 d2" .
    
    have "\<exists>(d1::real) (d2::real). d1 \<in> {l1..u1} \<and> d2 \<in> {l2..u2} \<and> (f * g) x = ?a + ?b d1 + ?c d2 + ?d  d1 d2"
      by ((rule exI)+, rule conjI[OF d1_def(1) conjI[OF d2_def(1) f_times_g_eq]])
  }
  
  show "valid_tm S (f * g) (TMMul t1 t2 I)"
    sorry
qed

(* Compute taylor models of degree n from floatarith expressions. *)
fun compute_taylor_model :: "nat \<Rightarrow> real interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "compute_taylor_model _ I (Num c) = Some (TaylorModel (poly.C c) (Ivl 0 0))"
    | "compute_taylor_model _ I (Var n) = Some (TaylorModel (poly.Bound n) (Ivl 0 0))"
    | "compute_taylor_model n I (Add a b) = (
         case (compute_taylor_model n I a, compute_taylor_model n I b) 
         of (Some t1, Some t2) \<Rightarrow> Some (TMAdd t1 t2) | _ \<Rightarrow> None
       )"
    | "compute_taylor_model n I (Minus a) = (
         case compute_taylor_model n I a of Some t1 \<Rightarrow> Some (TMNeg t1) | _ \<Rightarrow> None
       )"
    | "compute_taylor_model n I _ = None"
    
lemma
shows "\<And>t. Some t = compute_taylor_model n I f \<Longrightarrow> valid_tm (map set_of I) (interpret_floatarith f) t"
apply(induct f rule: compute_taylor_model.induct)
prefer 3
proof-
  fix n I a b t
  assume assms:
    "(\<And>t. Some t = compute_taylor_model n I a \<Longrightarrow> valid_tm (map set_of I) (interpret_floatarith a) t)"
    "(\<And>t. Some t = compute_taylor_model n I b \<Longrightarrow> valid_tm (map set_of I) (interpret_floatarith b) t)"
    "Some t = compute_taylor_model n I (floatarith.Add a b)"
    
  obtain t1 where t1_def: "Some t1 = compute_taylor_model n I a"
    by (metis (no_types, lifting) assms(3) compute_taylor_model.simps(3) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "Some t2 = compute_taylor_model n I b"
    by (smt assms(3) compute_taylor_model.simps(3) option.case_eq_if option.collapse prod.case)
    
  have t_def: "t = TMAdd t1 t2"
    using assms(3) t1_def t2_def
    by (metis compute_taylor_model.simps(3) option.case(2) option.inject prod.case)
  
  have [simp]: "interpret_floatarith (floatarith.Add a b) = interpret_floatarith a + interpret_floatarith b"
    by auto
  show "valid_tm (map set_of I) (interpret_floatarith (floatarith.Add a b)) t"
    by (simp add: t_def, rule TMAdd_valid[OF assms(1)[OF t1_def] assms(2)[OF t2_def]])
next
   fix n I a t
   assume assms:
     "\<And>t. Some t = compute_taylor_model n I a \<Longrightarrow> valid_tm (map set_of I) (interpret_floatarith a) t"
     "Some t = compute_taylor_model n I (Minus a)"
   have [simp]: "interpret_floatarith (Minus a) = -interpret_floatarith a"
     by auto
   
   obtain t1 where t1_def: "Some t1 = compute_taylor_model n I a"
     by (metis assms(2) compute_taylor_model.simps(4) option.collapse option.simps(4))
   have t_def: "t = TMNeg t1"
     by (metis assms(2) compute_taylor_model.simps(4) option.case(2) option.inject t1_def)
     
   show "valid_tm (map set_of I) (interpret_floatarith (Minus a)) t"
     by (simp add: t_def, rule TMNeg_valid[OF assms(1)[OF t1_def]])
qed (simp_all add: valid_tm_def)


end