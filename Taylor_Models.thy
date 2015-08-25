theory Taylor_Models
imports "~~/src/HOL/Decision_Procs/Reflected_Multivariate_Polynomial"
        "~~/src/HOL/Decision_Procs/Approximation"
        "~~/src/HOL/Library/Function_Algebras"
        "~~/src/HOL/Library/Set_Algebras"
        (*"/home/christoph/Documents/Studium/Interdisziplinäres Projekt/afp-linode/thys/Affine_Arithmetic/Affine_Arithmetic"*)
begin

(* Playing with approximations and interval arithmetic. *)
term "Num 0"
term "Less (Num 0) (Num 1)"
term "eval (Num 0)"
term "approx 10 ((Add (Num 0) (Num 1))) []"
approximate "arctan 1.5"
approximate "sin 3"

value "{0..Suc 0} + {Suc 0..2}"
(*value "{0..1}::real set"*)
  
ML {*
val abc = Thm.global_cterm_of @{theory} @{term "Add (Num 1) (Num 2)"};
Reification.tac @{context} [] NONE 0;
*}

lemma "arctan 1.5 < 1"
by (approximation 10)

(* Trying out multivariate polynomials.*)
value "Ipoly [x\<^sub>0::real, x\<^sub>1, x\<^sub>2, x\<^sub>3] (poly.Add ((poly.Pw (poly.Bound 2) 3)) (poly.Mul (poly.Bound 0) (poly.Bound 1)))"

value "Ipoly [x\<^sub>0::real, x\<^sub>1] (poly.Add (poly.Pw (poly.Bound 0) 2) (poly.Mul (poly.C (2, 2)) (poly.Pw (poly.Bound 1) 3)))"

value "\<lambda>x\<^sub>0 x\<^sub>1. Ipoly [x\<^sub>0::real, x\<^sub>1] (poly.Add (poly.Pw (poly.Bound 0) 2) (poly.Mul (poly.C (2, 2)) (poly.Pw (poly.Bound 1) 3)))"

value "polynate ((poly.Add ((poly.Pw (poly.Bound 2) 3)) (poly.Mul (poly.Bound 0) (poly.Bound 1))))"
thm polynate_norm

value "Float 1 2"


(* I define my own interval type here. TODO: Do I really need to do this? *)
datatype 'a interval = Ivl 'a 'a

definition lower :: "'a interval \<Rightarrow> 'a"
where "lower i = (case i of (Ivl l u) \<Rightarrow> l)"

definition upper :: "'a interval \<Rightarrow> 'a"
where "upper i = (case i of (Ivl l u) \<Rightarrow> u)"

definition set_of :: "('a::ord) interval \<Rightarrow> 'a set"
where "set_of i = (case i of (Ivl l u) \<Rightarrow> {l..u})"

declare lower_def[simp] upper_def[simp] set_of_def[simp]


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

declare plus_interval_def[simp] times_interval_def[simp]

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
where "compute_bound p I = (case approx 32 p (map (\<lambda>i. case i of Ivl a b \<Rightarrow> Some (a, b)) I) of Some (a, b) \<Rightarrow> Some (Ivl a b) | _ \<Rightarrow> None)"

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
  moreover have "Some (l, u) = approx 32 f (map Some (zip a b))"
    proof(rule ccontr)
      assume contr_assm: "Some (l, u) \<noteq> approx 32 f (map Some (zip a b))"
      have [simp]: "map (case_interval (\<lambda>a b. Some (a, b)) \<circ> (\<lambda>(x, y). Ivl x y)) (zip a b) = map Some (zip a b)"
        by auto
      show False
        proof(cases "approx 32 f (map Some (zip a b))")
          assume "approx 32 f (map Some (zip a b)) = None"
          from assms(1)[unfolded compute_bound.simps I_def, simplified, unfolded this]
          show "False"
            by auto
        next
          fix ab' assume assm: "approx 32 f (map Some (zip a b)) = Some ab'"
          obtain a' b' where ab'_def: "ab' = (a', b')"
            using old.prod.exhaust by blast
          from assms(1)[unfolded compute_bound.simps I_def, simplified, unfolded assm this, simplified]
          show False using contr_assm assm by (simp add: ab'_def)
        qed
    qed
  ultimately show ?thesis
    using approx by auto
qed

(* Taylor models are a tupel of an approximation polynomial and error bound (an interval).
   TODO: Generalize! For now, we only implement univariate taylor models. *)
datatype taylor_model = TaylorModel floatarith "float interval"

definition valid_tm :: "real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> bool"
where "valid_tm S f t = (case t of (TaylorModel p (Ivl l u)) \<Rightarrow> \<forall>x\<in>S. f x - interpret_floatarith p [x] \<in> {l..u})"

lemma valid_tmD[elim]:
assumes "valid_tm S f t"
obtains p l u
where "t = TaylorModel p (Ivl l u)"
and   "\<And>x. x \<in> S \<Longrightarrow> f x - interpret_floatarith p [x] \<in> {l..u}"
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
and   "\<And>x. x \<in> S \<Longrightarrow> f x - interpret_floatarith p [x] \<in> {l..u}"
shows "valid_tm S f t"
using assms by (auto simp: valid_tm_def)

(* Operations on taylor models. *)
fun TMNeg :: "taylor_model \<Rightarrow> taylor_model"
where "TMNeg (TaylorModel p (Ivl l u)) = TaylorModel (Minus p) (Ivl (-u) (-l))"

fun TMAdd :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMAdd (TaylorModel p1 i1) (TaylorModel p2 i2) = TaylorModel (Add p1 p2) (i1+i2)"

fun TMSub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMSub t1 t2 = TMAdd t1 (TMNeg t2)"

(*fun TMMul :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> float interval \<Rightarrow> taylor_model"
where "TMMul (TaylorModel p1 i1) (TaylorModel p2 i2) I = TaylorModel (Mult p1 p2) (i1+i2)"*)

(* Validity of taylor models is preserved under these operations. *)
lemma TMNeg_valid:
assumes "valid_tm S f t"
shows "valid_tm S (-f) (TMNeg t)"
proof-
  from valid_tmD[OF assms]
  obtain p l u where t_def: "t = TaylorModel p (Ivl l u)" "\<And>x. x \<in> S \<Longrightarrow> f x - interpret_floatarith p [x] \<in> {l..u}"
    by auto
  show ?thesis
    apply(rule)
    apply(simp add: t_def(1))
    proof-
      fix x assume "x \<in> S"
      show "(- f) x - (interpret_floatarith (Minus p) [x]) \<in> {-u..-l}"
        using t_def(2)[OF `x \<in> S`] by simp
    qed
qed

lemma TMAdd_valid:
assumes "valid_tm S f t1"
assumes "valid_tm S g t2"
shows "valid_tm S (f + g) (TMAdd t1 t2)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 l1 u1 where t1_def: "t1 = TaylorModel p1 (Ivl l1 u1)" "\<And>x. x \<in> S \<Longrightarrow> f x - interpret_floatarith p1 [x] \<in> {l1..u1}"
    by auto
  from valid_tmD[OF assms(2)]
  obtain p2 l2 u2 where t2_def: "t2 = TaylorModel p2 (Ivl l2 u2)" "\<And>x. x \<in> S \<Longrightarrow> g x - interpret_floatarith p2 [x] \<in> {l2..u2}"
    by auto
  show "valid_tm S (f + g) (TMAdd t1 t2)"
    proof(rule, simp add: t1_def(1) t2_def(1))
      fix x assume "x \<in> S"
      from t1_def(2)[OF this] t2_def(2)[OF this]
       show "(f + g) x - (interpret_floatarith (Add p1 p2) [x]) \<in> {(l1+l2)..(u1+u2)}"
        by simp
    qed
qed

lemma TMSub_valid:
assumes "valid_tm S f t1"
assumes "valid_tm S g t2"
shows "valid_tm S (f - g) (TMSub t1 t2)"
using TMAdd_valid[OF assms(1) TMNeg_valid[OF assms(2)]]
by simp



end