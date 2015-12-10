theory Taylor_Models
imports "Intervals"
        "Horner_Eval"
        "Poly_Ex"
        "Taylor_Models_Misc"
        "~~/src/HOL/Decision_Procs/Approximation"
        "~~/src/HOL/Library/Function_Algebras"
        "~~/src/HOL/Library/Set_Algebras"
begin

section \<open>Multivariate Taylor Models\<close>

subsection \<open>Computing interval bounds on arithmetic expressions\<close>

fun compute_bound_fa :: "nat \<Rightarrow> floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_bound_fa prec f I = (case approx prec f (map (Some o proc_of) I) of Some (a, b) \<Rightarrow> (if a \<le> b then Some (Ivl a b) else None) | _ \<Rightarrow> None)"

lemma compute_bound_fa_correct:
fixes i::"real list"
assumes "i all_in I"
assumes "Some ivl = compute_bound_fa prec f I"
shows "interpret_floatarith f i \<in> set_of ivl"
proof-
  have "\<forall>n < length I. \<exists>a b. I!n = Ivl a b \<and> a \<le> b"
    proof(safe)
      fix n assume "n < length I"
      obtain a b where ab_def: "I!n = Ivl a b" "a \<le> b" using interval_exhaust by blast
      thus "\<exists>a b. I ! n = Ivl a b \<and> a \<le> b"
        by auto
    qed
  then obtain fa fb where I_def': "\<And>n. n < length I \<Longrightarrow> I!n = Ivl (fa n) (fb n) \<and> fa n \<le> fb n"
    by (auto simp: choice_iff')
    
  def a\<equiv>"map (\<lambda>x. fa (nat x)) ([0..<length I])"
  def b\<equiv>"map (\<lambda>x. fb (nat x)) ([0..<length I])"
  
  have length_a: "length a = length I"
    by (simp add: a_def)
  have length_b: "length b = length I"
    by (simp add: b_def)
    
  have an_le_bn: "\<And>n. n < length I \<Longrightarrow> a!n \<le> b!n"
    using I_def' a_def b_def by auto
    
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
    
  obtain l u where ivl_def: "ivl = Ivl l u" and l_le_u: "l \<le> u" using interval_exhaust by blast
    
  have "bounded_by i (map Some (zip a b))"
    proof(simp add: bounded_by_def length_a length_b, safe)
      fix n assume "n < length I"
      from `i all_in I` this
      have concl: "i ! n \<in> {(a!n)..(b!n)}"           
        using `n < length I` an_le_bn by (auto simp: I_def set_of_def)
      
      show "(a ! n) \<le> i ! n"
        using concl by simp
      show "i ! n \<le> real_of_float (b ! n)"
        using concl by simp
    qed
  moreover have "Some (l, u) = approx prec f (map Some (zip a b))"
    proof(rule ccontr)
      assume contr_assm: "Some (l, u) \<noteq> approx prec f (map Some (zip a b))"
      have domain_simp: "map (Some \<circ> proc_of) (map (\<lambda>(x, y). Ivl x y) (zip a b)) = map Some (zip a b)"
        using an_le_bn
        apply(simp)
        apply(safe)
        apply(subst Ivl.rep_eq)
        apply(simp add: max_def)
        by (metis fst_conv in_set_zip length_a snd_conv)
      show False
        proof(cases "approx prec f (map Some (zip a b))")
          assume assm: "approx prec f (map Some (zip a b)) = None"
          from assms(2)[unfolded compute_bound_fa.simps I_def]
          show "False"
            unfolding domain_simp
            by (simp add: assm case_prod_beta comp_def)
        next
          fix ab' assume assm: "approx prec f (map Some (zip a b)) = Some ab'"
          then obtain a' b' where ab'_def: "ab' = (a', b')" by fastforce
          hence "(a', b') \<noteq> (l, u)" using contr_assm assm by auto
          from assms(2)[unfolded compute_bound_fa.simps I_def] this assm
          show False
            unfolding domain_simp
            apply(cases "a' \<le> b'")
            apply(simp_all add: ab'_def ivl_def case_prod_beta comp_def)
            by (metis l_le_u less_eq_float.rep_eq lower_Ivl upper_Ivl_b)
        qed
    qed
  ultimately show ?thesis
    using approx l_le_u by (auto simp: ivl_def set_of_def)
qed


subsection \<open>Definition of taylor models and notion of validity\<close>

(* Taylor models are a pair of a polynomial and an absolute error bound. *)
datatype taylor_model = TaylorModel "float poly" "float interval"

(* A taylor model of function f on interval I is valid, iff
     - its polynomial has the right number of parameters
     - and it is close to f on I.
*)
primrec valid_tm :: "float interval list \<Rightarrow> float list \<Rightarrow> (real list \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> bool"
where "valid_tm I a f (TaylorModel p e) = (num_params p \<le> length I \<and> a all_in I \<and> (\<forall>x. x all_in I \<longrightarrow> f x - Ipoly (list_op op- x a) (p::real poly) \<in> set_of e))"

lemma valid_tmD[elim]:
assumes "valid_tm I a f t"
obtains p e
where "t = TaylorModel p e"
and   "num_params p \<le> length I"
and   "a all_in I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly (list_op op- x a) (p::real poly) \<in> set_of e"
proof-
  obtain p e where t_decomp: "t = TaylorModel p e" using taylor_model.exhaust by auto
  moreover have "num_params p \<le> length I"
           and  "a all_in I"
           and  "\<And>x. x all_in map (interval_map real_of_float) I \<Longrightarrow> f x - Ipoly (list_op op- x a) (p::real poly) \<in> set_of (interval_map real_of_float e)"
    using assms
    by (auto simp: t_decomp)
  ultimately show ?thesis
    using that by simp  
qed

lemma valid_tmD':
assumes "valid_tm I a f t"
and "t = TaylorModel p e"
shows "num_params p \<le> length I"
and   "a all_in I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly (list_op op- x a) (p::real poly) \<in> set_of e"
using valid_tmD[OF assms(1)] assms(2)
by auto

lemma valid_tmI[intro]:
assumes "t = TaylorModel p e"
and   "num_params p \<le> length I"
and   "a all_in I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly (list_op op- x a) (p::real poly) \<in> set_of e"
shows "valid_tm I a f t"
using assms by (auto simp: valid_tm_def)

lemma valid_tm_subset:
assumes "I all_subset J"
assumes "a all_in I"
assumes "valid_tm J a f t"
shows "valid_tm I a f t"
proof-
  from assms(1) have I_in_J: "I all_subset (J::real interval list)"
    by (simp add: set_of_def interval_map_def)
  obtain p e where t_decomp: "t = TaylorModel p e"
    using taylor_model.exhaust by auto
  
  from \<open>I all_subset J\<close> have [simp]: "length I = length J" by simp
    
  show ?thesis
    apply(rule valid_tmI[OF t_decomp _ assms(2)])
    using valid_tmD'(1)[OF assms(3) t_decomp]
    apply(simp)
    apply(drule all_subsetD[OF I_in_J])
    using valid_tmD'(3)[OF assms(3) t_decomp]
    by simp
qed


subsection \<open>Interval bounds for taylor models\<close>

(* Bound a polynomial by simply evaluating it with interval arguments. *)
fun compute_bound_poly :: "float poly \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float interval"
where "compute_bound_poly p I a = Ipoly (list_op op- I a) p"

fun compute_bound_tm :: "float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> float interval"
where "compute_bound_tm I a (TaylorModel p e) = compute_bound_poly p I a + e"

lemma compute_bound_poly_correct:
fixes p::"float poly"
assumes "num_params p \<le> length I"
assumes "x all_in I"
assumes "a all_in I"
shows "Ipoly (list_op op- x a) (p::real poly) \<in> set_of (compute_bound_poly p I a)"
proof-
  have [simp]: "length x = length a"
    using assms(2,3) by simp

  have "Ipoly (list_op op- x (map real_of_float a)) (poly_map real_of_float p) \<in> set_of (Ipoly (list_op op- I (map interval_of a)) (poly_map interval_of (poly_map real_of_float p)))"
    apply(rule Ipoly_interval_args_mono)
    apply(simp)
    apply(safe)
    using assms(2)
    apply simp
    apply(rule set_of_minus_mono)
    using assms
    by simp_all
  also have "... = set_of (interval_map real_of_float (Ipoly (list_op op- I (map interval_of a)) (poly_map interval_of p)))"
    apply(rule arg_cong[where f=set_of])
    using assms(1,2)
    by (induction p, simp_all)
  finally show ?thesis
    by simp
qed

lemma compute_bound_poly_mono:
assumes "num_params p \<le> length I"
assumes "I all_subset J"
assumes "a all_in I"
shows "set_of (compute_bound_poly p I a) \<subseteq> set_of (compute_bound_poly p J a)"
apply simp
apply(rule Ipoly_interval_args_inc_mono)
using assms
by (simp_all add: set_of_sub_inc_left)

lemma compute_bound_tm_correct:
fixes I :: "float interval list" and x :: "real list" and f :: "real list \<Rightarrow> real"
assumes "valid_tm I a f t"
assumes "x all_in I"
shows "f x \<in> set_of (compute_bound_tm I a t)"
proof-
  obtain p l u where t_decomp: "t = TaylorModel p (Ivl l u)"
    by (metis interval_exhaust taylor_model.exhaust)
    
  from valid_tmD'[OF assms(1) t_decomp] assms(2) have valid:
    "num_params p \<le> length I"
    "a all_in I"
    "f x - Ipoly (list_op op- x (map real_of_float a)) p
      \<in> set_of (Ivl l u)"
      by auto
  
  show "f x \<in> set_of (compute_bound_tm I a t)"
    using set_of_add_mono[OF compute_bound_poly_correct[OF valid(1) assms(2) \<open>a all_in I\<close>] valid(3)]
    by (simp add: t_decomp)
qed

lemma compute_bound_tm_mono:
fixes I :: "float interval list" and x :: "real list" and f :: "real list \<Rightarrow> real"
assumes "valid_tm I a f t"
assumes "I all_subset J"
assumes "a all_in I"
shows "set_of (compute_bound_tm I a t) \<subseteq> set_of (compute_bound_tm J a t)"
apply(cases t, simp del: compute_bound_poly.simps)
apply(rule set_of_add_inc_left)
apply(rule compute_bound_poly_mono[OF _ assms(2,3)])
using assms(1)
by simp


subsection \<open>Computing taylor models for basic, univariate functions\<close>

fun tm_const :: "float \<Rightarrow> taylor_model"
where "tm_const c = TaylorModel (poly.C c) (Ivl 0 0)"

fun tm_var :: "nat \<Rightarrow> float list \<Rightarrow> taylor_model"
where "tm_var i a = TaylorModel (poly.CN (poly.C (a!i)) i (poly.C 1)) (Ivl 0 0)"

fun tm_pi :: "nat \<Rightarrow> taylor_model"
where "tm_pi prec = (
  let pi_ivl = the (compute_bound_fa prec Pi [])
  in TaylorModel (poly.C (mid pi_ivl)) (centered pi_ivl)
)"

lemma tm_const_valid:
assumes "a all_in I"
shows "valid_tm I a (interpret_floatarith (Num c)) (tm_const c)"
using assms
by simp

lemma tm_var_valid:
assumes "n < length I"
assumes "a all_in I"
shows "valid_tm I a (interpret_floatarith (Var n)) (tm_var n a)"
using assms by simp

lemma tm_pi_valid:
assumes "a all_in I"
shows "valid_tm I a (interpret_floatarith Pi) (tm_pi prec)"
proof-
  have "\<And>prec. real_of_float (lb_pi prec) \<le> real_of_float (ub_pi prec)"
    using iffD1[OF atLeastAtMost_iff, OF pi_boundaries]
    using order_trans by auto
  then obtain ivl_pi where ivl_pi_def: "Some ivl_pi = compute_bound_fa prec Pi []"
    by (simp add: approx.simps)
  show ?thesis
    apply(rule valid_tmI[OF _ _ assms])
    apply(simp add: Let_def del: compute_bound_fa.simps)
    apply(simp)
    unfolding ivl_pi_def[symmetric]
    using compute_bound_fa_correct[of "[]" "[]", OF _ ivl_pi_def, simplified]
    by (simp, simp add: minus_interval_def set_of_def)
qed


subsubsection \<open>Derivations of floatarith expressions\<close>

definition Sin::"floatarith \<Rightarrow> floatarith"
where "Sin x = Cos (Add x (Mult Pi (Num (Float (-1) (- 1)))))"

(* Compute the nth derivative of a floatarith expression *)
fun deriv :: "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
where "deriv v f 0 = f"
    | "deriv v f (Suc n) = DERIV_floatarith v (deriv v f n)"

lemma isDERIV_DERIV_floatarith:
assumes "isDERIV v f vs"
shows "isDERIV v (DERIV_floatarith v f) vs"
using assms
apply(induction f)
apply(simp_all add: numeral_eq_Suc add_nonneg_eq_0_iff)
proof-
  fix f m assume hyp: "isDERIV v f vs \<Longrightarrow> isDERIV v (DERIV_floatarith v f) vs"
  show "isDERIV v (Power f m) vs \<Longrightarrow> isDERIV v (DERIV_floatarith v (Power f m)) vs"
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

(* Faster derivation for univariate functions, producing smaller terms and thus less over-approximation. *)
(* TODO: Extend to Arctan, Exp, Log! *)
fun deriv_0 :: "floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
where "deriv_0 (Cos (Var 0)) n = (case n mod 4
         of 0 \<Rightarrow> Cos (Var 0)
         | Suc 0 \<Rightarrow> Minus (Sin (Var 0))
         | Suc (Suc 0) \<Rightarrow> Minus (Cos (Var 0))
         | Suc (Suc (Suc 0)) \<Rightarrow> Sin (Var 0))"
    | "deriv_0 (Inverse (Var 0)) n = (if n = 0 then Inverse (Var 0) else Mult (Num (fact n * (if n mod 2 = 0 then 1 else -1))) (Inverse (Power (Var 0) (Suc n))))"
    | "deriv_0 f n = deriv 0 f n"

lemma deriv_0_correct:
assumes "isDERIV 0 f [t]"
shows "((\<lambda>x. interpret_floatarith (deriv_0 f n) [x]) has_real_derivative interpret_floatarith (deriv_0 f (Suc n)) [t]) (at t)"
apply(cases "(f, n)" rule: deriv_0.cases)
apply(safe)
using assms deriv_correct[OF assms]
proof-
  assume "f = Cos (Var 0)"
  
  have n_mod_4_cases: "n mod 4 = 0 | n mod 4 = 1 | n mod 4 = 2 | n mod 4 = 3"
    by auto
  have Sin_sin: "(\<lambda>xs. interpret_floatarith (Sin (Var 0)) xs) = (\<lambda>xs. sin (xs!0))"
    apply(simp add: Sin_def sin_cos_eq)
    apply(subst (2) cos_minus[symmetric])
    by simp
  show "((\<lambda>x. interpret_floatarith (deriv_0 (Cos (Var 0)) n) [x]) has_real_derivative
         interpret_floatarith (deriv_0 (Cos (Var 0)) (Suc n)) [t])
         (at t)"
    using n_mod_4_cases
    apply(safe)
    apply(simp_all add: mod_Suc_eq_Suc_mod[of n 4] Sin_sin field_differentiable_minus)
    using DERIV_cos field_differentiable_minus by fastforce
next
  assume f_def: "f = Inverse (Var 0)" and "isDERIV 0 f [t]"
  hence "t \<noteq> 0"
    by simp
  {
    fix n::nat and x::real
    assume "x \<noteq> 0"
    moreover have "(n mod 2 = 0 \<and> Suc n mod 2 = 1) \<or> (n mod 2 = 1 \<and> Suc n mod 2 = 0)"
      apply(simp)
      apply(safe)
      apply(simp_all)
      by (presburger)+
    ultimately have "interpret_floatarith (deriv_0 f n) [x] = fact n * (-1::real)^n / (x^Suc n)"
      apply(safe)
      apply(simp_all add: f_def field_simps)
      apply(safe)
      using fact_real_float_equiv 
      apply simp_all
      proof(goal_cases)
        case (1 q)
        hence n_decomp: "n = (q-1) * 2 + 1"
          by simp
        thus ?case
          using fact_real_float_equiv
          by simp
      qed
  }
  note closed_formula = this
  
  have "((\<lambda>x. inverse (x ^ Suc n)) has_real_derivative -real (Suc n) * inverse (t ^ Suc (Suc n))) (at t)"
    using DERIV_inverse_fun[OF DERIV_pow[where n="Suc n"], where s=UNIV]
    apply(rule iffD1[OF DERIV_cong_ev[OF refl], rotated 2])
    using `t \<noteq> 0`
    by (simp_all add: divide_simps)
  hence "((\<lambda>x. fact n * (-1::real)^n * inverse (x ^ Suc n)) has_real_derivative fact (Suc n) * (- 1) ^ Suc n / t ^ Suc (Suc n)) (at t)"
    apply(rule iffD1[OF DERIV_cong_ev, OF refl _ _ DERIV_cmult[where c="fact n * (-1::real)^n"], rotated 2])
    using `t \<noteq> 0`
    by (simp_all add: field_simps distrib_left)
  thus "((\<lambda>x. interpret_floatarith (deriv_0 (Inverse (Var 0)) n) [x]) has_real_derivative
         interpret_floatarith (deriv_0 (Inverse (Var 0)) (Suc n)) [t])
         (at t)"
    apply(rule iffD1[OF DERIV_cong_ev[OF refl _ closed_formula[OF `t \<noteq> 0`, symmetric]], unfolded f_def, rotated 1])
    by (simp, safe, simp_all add: fact_real_float_equiv inverse_eq_divide even_iff_mod_2_eq_zero)
qed (simp_all)

lemma deriv_0_0_idem[simp]:
shows "deriv_0 f 0 = f"
by (cases "(f, 0::nat)" rule: deriv_0.cases, simp_all)


subsubsection \<open>Computing taylor models for arbitrary univariate expressions\<close> 

(* The interval coefficients of the taylor polynomial,
   i.e. the real coefficients approximated by a float interval. *)
fun tmf_c :: "nat \<Rightarrow> float interval \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> float interval option"
where "tmf_c prec I f i = compute_bound_fa prec (Mult (deriv_0 f i) (Inverse (Num (fact i)))) [I]"

(* Make a list of the n+1 coefficients, with the n+1-th coefficient representing the error contribution.*)
fun tmf_ivl_cs :: "nat \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> float interval list option"
where "tmf_ivl_cs prec ord I a f = those (map (tmf_c prec a f) [0..<ord] @ [tmf_c prec I f ord])"

fun tmf_polys :: "float interval list \<Rightarrow> float poly \<times> float interval poly"
where "tmf_polys [] = (poly.C 0, poly.C 0)"
    | "tmf_polys (c # cs) = (
         let (pf, pi) = tmf_polys cs
         in (poly.CN (poly.C (mid c)) 0 pf, poly.CN (poly.C (centered c)) 0 pi)
       )"

(* Compute a taylor model from an arbitrary, univariate floatarith expression, if possible.
   This is used to compute taylor models for elemental functions like sin, cos, exp, etc. *)
fun tm_floatarith :: "nat \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "tm_floatarith prec ord I a f = (
  map_option (\<lambda>cs. 
    let (pf, pi) = tmf_polys cs;
        e = round_ivl prec (Ipoly [I - a] pi)
    in TaylorModel pf e
  ) (tmf_ivl_cs prec ord I a f)
)"

lemma tmf_c_correct:
fixes A::"float interval" and I::"float interval" and f::floatarith and a::real
assumes "a \<in> set_of A"
assumes "Some I = tmf_c prec A f i"
shows "interpret_floatarith (deriv_0 f i) [a] / fact i \<in> set_of I"
using compute_bound_fa_correct[OF _  assms(2)[unfolded tmf_c.simps], where i="[a]"] assms(1)
by (simp add: divide_real_def fact_real_float_equiv)

lemma tmf_ivl_cs_length:
assumes "Some cs = tmf_ivl_cs prec n A a f"
shows "length cs = n + 1"
by (simp add: Some_those_length[OF assms[unfolded tmf_ivl_cs.simps]])

lemma tmf_ivl_cs_correct:
fixes A::"float interval" and f::floatarith
assumes "a \<in> set_of I"
assumes "Some cs = tmf_ivl_cs prec ord I a f"
shows "\<And>i. i < ord \<Longrightarrow> Some (cs!i) = tmf_c prec (interval_of a) f i"
and   "Some (cs!ord) = tmf_c prec I f ord"
proof-
  from tmf_ivl_cs_length[OF assms(2)]
  show "Some (cs!ord) = tmf_c prec I f ord"
    by (simp add: Some_those_nth assms(2) nth_append)
next
  fix i assume "i < ord"
  have "Some (cs!i) = (map (tmf_c prec a f) [0..<ord] @ [tmf_c prec I f ord]) ! i"
    apply(rule Some_those_nth)
    using assms(2) tmf_ivl_cs_length \<open>i < ord\<close>
    by simp_all
  then show "Some (cs!i) = tmf_c prec a f i" 
    using \<open>i < ord\<close>
    by (simp add: nth_append)
qed

(* TODO: Clean this up! *)
lemma tm_floatarith_valid:
assumes "a \<in> set_of I"
assumes "\<And>x. x \<in> set_of I \<Longrightarrow> isDERIV 0 f [x]"
assumes "Some t = tm_floatarith prec ord I a f"
shows "valid_tm [I] [a] (interpret_floatarith f) t"
proof(cases "ord = 0")
  case True
  thm assms(3)[unfolded True, simplified]
  obtain cs where tmf_cs_decomp: "tmf_ivl_cs prec ord I a f = Some cs"
    using assms(3) by fastforce
  moreover have tmf_cs_decomp': "tmf_ivl_cs prec ord I a f = those [tmf_c prec I f ord]"
    by (simp add: True)
  ultimately obtain c where tmf_c_decomp: "tmf_c prec I f ord = Some c"
    by fastforce
  hence "cs = [c]"
    using tmf_cs_decomp tmf_cs_decomp' by auto
  
  show ?thesis
    using assms(3)
    unfolding tm_floatarith.simps tmf_cs_decomp
    apply(simp add: \<open>cs = [c]\<close> del: round_ivl.simps)
    apply(safe)
    apply(rule assms(1))
    apply(rule subsetD[OF real_of_float_round_ivl_correct])
    apply(drule tmf_c_correct[OF _ tmf_c_decomp[symmetric], simplified \<open>ord = 0\<close>, simplified])
    apply(simp)
    apply(rule set_of_minus_mono)
    apply(simp_all)
    by (smt Suc_length_conv length_0_conv nth_Cons_0)
next
  case False
  hence "0 < ord" by simp
  obtain cs where cs_def: "Some cs = tmf_ivl_cs prec ord I a f"
    using assms(3)[unfolded tm_floatarith.simps, symmetric]
      by auto
  from assms(3)[unfolded tm_floatarith.simps] 
  obtain pf pi where pf_pi_def: "(pf, pi) = tmf_polys cs"
    unfolding cs_def[symmetric]
    using prod.collapse by blast
  
  have t_def: "t = TaylorModel pf (round_ivl prec (Ipoly [I - interval_of a] pi))"
    using assms(3)[unfolded tm_floatarith.simps]
    unfolding cs_def[symmetric]
    by (simp add: pf_pi_def[symmetric])
  
  show ?thesis
  proof(rule valid_tmI)
    show "t = TaylorModel pf (round_ivl prec (Ipoly [I - interval_of a] pi))"
      by (simp add: t_def)
  next
    show "num_params pf \<le> length [I]"
      using pf_pi_def
      apply(induction cs arbitrary: pf pi)
      apply(simp)
      proof-
        case (Cons c cs pf pi)
        then obtain pf' pi' where pf'pi'_def: "(pf', pi') = tmf_polys cs"
          using prod.collapse by blast
        from this Cons(2)[unfolded tmf_polys.simps]
        have pf_decomp: "pf = poly.CN (mid c)\<^sub>p 0 pf'"
          by (metis old.prod.case prod.sel(1))
        show ?case
          using Cons(1)[OF pf'pi'_def]
          by (simp add: pf_decomp)
      qed
  next
    fix xs assume hyp: "xs all_in map (interval_map real_of_float) [I]"
    from hyp obtain x where xs_def: "xs = [x]" by (auto simp: length_Suc_conv)
    hence x_in_I: "x \<in> set_of I" using hyp by simp
    
    have "interpret_floatarith f xs - Ipoly (list_op op- xs [a]) pf
         \<in> set_of (interval_map real_of_float (Ipoly [I - interval_of a] pi))"
    proof(cases "x = a")
      case True
      have pf_val_at_a: "Ipoly (list_op op- xs [a]) pf = mid (cs ! 0)"
        using pf_pi_def tmf_ivl_cs_length[OF cs_def]
        apply(induction cs arbitrary: pf pi ord)
        apply(simp)
        proof-
          case (Cons c cs pf pi ord)
          then obtain pf' pi' where pf'pi'_def: "(pf', pi') = tmf_polys cs"
            using prod.collapse by blast
          from this Cons(2)[unfolded tmf_polys.simps]
          have pf_decomp: "pf = poly.CN (mid c)\<^sub>p 0 pf'"
            by (metis old.prod.case prod.sel(1))
          show ?case
            using Cons(1)[OF pf'pi'_def]
            by (simp add: pf_decomp True xs_def)
        qed
      have "interpret_floatarith f xs - Ipoly (list_op op- xs [a]) pf \<in> set_of (interval_map real_of_float (cs ! 0) - (mid (cs ! 0)))"
        apply(rule set_of_minus_mono)
        using pf_val_at_a tmf_c_correct[OF _ tmf_ivl_cs_correct(1)[OF assms(1) cs_def `0 < ord`], of a]
        by (simp_all add: xs_def `x = a` set_of_def)
      also have "... \<subseteq>  set_of (interval_map real_of_float (Ipoly [I - interval_of a] pi))"
        proof-
          from tmf_ivl_cs_length[OF cs_def]
          obtain c cs' where cs_decomp: "cs = c # cs'" 
            by (metis Suc_eq_plus1 list.size(3) neq_Nil_conv old.nat.distinct(2))
          obtain pi' where pi_decomp: "pi = poly.CN (c - interval_of (mid c))\<^sub>p 0 pi'"
            using pf_pi_def
            by (simp add: cs_decomp case_prod_beta)
          show ?thesis
            apply(simp add: cs_decomp pi_decomp)
            apply(rule set_of_add_inc[where B=0, simplified])
            apply(simp add: zero_interval_def)
            apply(simp add: set_of_def[of "Ivl 0 0"] zero_interval_def)
            apply(rule set_of_mul_contains_zero)
            apply(rule disjI1)
            apply(rule set_of_minus_mono[where a="a" and b="a" and A="interval_map real_of_float I", simplified])
            using assms(1)
            by (simp_all add: uminus_interval_def)
        qed
      finally show ?thesis .
    next
      case False
      
      obtain l u where I_def: "I = Ivl l u" and l_le_u: "l \<le> u" by (metis interval_exhaust) 
      
      have "\<exists>t. (if x < real_of_float a then x < t \<and> t < real_of_float a else real_of_float a < t \<and> t < x) \<and>
                interpret_floatarith f [x] =
                  (\<Sum>m<ord. interpret_floatarith (deriv_0 f m) [real_of_float a] / fact m * (x - real_of_float a) ^ m)
                  + interpret_floatarith (deriv_0 f ord) [t] / fact ord * (x - real_of_float a) ^ ord"
        apply(rule taylor[where a=l and b=u])
        apply(rule `0 < ord`)
        apply(simp)
        apply(safe)[1]
        apply(rule deriv_0_correct[OF assms(2)])
        apply(simp add: I_def)
        using assms(1) x_in_I `x \<noteq> a` l_le_u
        by (simp_all add: I_def set_of_def)
      then obtain t 
      where "if x < real_of_float a then x < t \<and> t < real_of_float a else real_of_float a < t \<and> t < x"
      and taylor_expansion:
        "interpret_floatarith f [x] = 
           (\<Sum>m<ord. interpret_floatarith (deriv_0 f m) [real_of_float a] / fact m * (x - real_of_float a) ^ m)
           + interpret_floatarith (deriv_0 f ord) [t] / fact ord * (x - real_of_float a) ^ ord"
        by auto
      from this(1) have t_in_I: "t \<in> set_of I"
        using assms(1) x_in_I l_le_u
        apply(simp add: I_def set_of_def)
        by (meson less_eq_real_def order_trans)
      
      from pf_pi_def tmf_ivl_cs_length[OF cs_def]
      have Ipoly_pf_eq: "Ipoly (list_op op- xs [a]) pf = (\<Sum>m<Suc ord. mid (cs!m) * (x - a) ^ m)"
        apply(induction cs arbitrary: ord pf pi)
        apply(simp add: xs_def)
        proof-
          case (Cons c cs ord pf pi)
          obtain pf' pi' where pf'pi'_def: "(pf', pi') = tmf_polys cs"
            using prod.collapse by blast
          from Cons(2)
          have pf_def: "pf = poly.CN (mid c)\<^sub>p 0 pf'"
          and  pi_def: "pi = poly.CN (c - interval_of (mid c))\<^sub>p 0 pi'"
            by (auto simp: pf'pi'_def[symmetric])
          from Cons(3) have [simp]: "length cs = ord" by simp
            
          show ?case
            apply(cases cs)
            using Cons(2,3)
            apply(simp)
            proof-
              fix c' cs' assume cs_def: "cs = c' # cs'"
              
              have "Ipoly (list_op op- xs [a]) pf = mid c + (x - a) * Ipoly [x - a] pf'"
                by (simp add: pf_def xs_def)
              also have "... = mid c + (x - a) * (\<Sum>m<Suc (length cs'). mid (cs ! m) * (x - a) ^ m)"
                using Cons(1)[OF pf'pi'_def, where ord="length cs'"]
                by (simp add: cs_def xs_def)
              also have "... = real_of_float (mid c) + (x - real_of_float a) * (\<Sum>m<length cs. real_of_float (mid ((c # cs) ! Suc m)) * (x - real_of_float a) ^ m)"
                by (simp add: cs_def)
              also have "... = real_of_float (mid c) + (\<Sum>m<ord. real_of_float (mid ((c # cs) ! Suc m)) * (x - real_of_float a) ^ Suc m)"
                by (simp add:  setsum_right_distrib linordered_field_class.sign_simps(25))
              also have "... = real_of_float (mid c) + (\<Sum>m\<in>{1..ord}. real_of_float (mid ((c # cs) ! m)) * (x - real_of_float a) ^ m)"
                apply(subst setsum_shift_bounds_Suc_ivl[symmetric, of _ 0 "ord", unfolded atLeast0LessThan])
                unfolding atLeastLessThanSuc_atLeastAtMost
                by simp
              also have "... = (\<Sum>m\<in>{0..ord}. real_of_float (mid ((c # cs) ! m)) * (x - real_of_float a) ^ m)"
                using setsum_add_nat_ivl[where m=0 and n=1 and p="Suc ord" and f="\<lambda>m. real_of_float (mid ((c # cs) ! m)) * (x - real_of_float a) ^ m", unfolded atLeastLessThanSuc_atLeastAtMost, simplified]
                by simp
              finally show "Ipoly (list_op op- xs [a]) pf = (\<Sum>m<Suc ord. mid ((c # cs) ! m) * (x - a)^m)"
                unfolding atLeast0AtMost lessThan_Suc_atMost
                by simp
            qed
        qed
      
      def cr\<equiv>"\<lambda>i. if i < ord then (interpret_floatarith (deriv_0 f i) [real_of_float a] / fact i - real_of_float (mid (cs ! i)))
                             else (interpret_floatarith (deriv_0 f i) [t] / fact ord - real_of_float (mid (cs ! i)))"
      def ci\<equiv>"\<lambda>i. (interval_map real_of_float (cs ! i) - interval_of (real_of_float (mid (cs ! i))))"
      
      have "(\<Sum>m<ord. interpret_floatarith (deriv_0 f m) [real_of_float a] / fact m * (x - a) ^ m)
                 + interpret_floatarith (deriv_0 f ord) [t] / fact ord * (x - a) ^ ord
                 - Ipoly (list_op (\<lambda>x xa. x - real_of_float xa) xs [a]) pf
                 = (\<Sum>m<ord. cr m  * (x - a) ^ m) + cr ord * (x - a) ^ ord"
        by (simp add: Ipoly_pf_eq algebra_simps setsum.distrib[symmetric] cr_def)
      also have "... = horner_eval cr (x - real_of_float a) (Suc ord)"
        by (simp add: horner_eval_eq_setsum)
      also have "... \<in> set_of (horner_eval ci (x - real_of_float a) (Suc ord))"
        apply(rule horner_eval_interval)
        apply(simp add: cr_def ci_def)
        apply(safe)[1]
        using tmf_c_correct[OF _ tmf_ivl_cs_correct(1)[OF assms(1) cs_def], where a=a, simplified]
        apply(simp)
        apply(rule set_of_minus_mono)
        using tmf_c_correct[OF t_in_I tmf_ivl_cs_correct(2)[OF assms(1) cs_def]]
        apply(simp_all)
        proof(goal_cases)
          case(1 i)
          hence "i = ord" by simp
          thus ?case
            apply(simp)
            apply(rule set_of_minus_mono[OF 1(3)])
            by simp
        qed
      also have "... \<subseteq> set_of (interval_map real_of_float (Ipoly [I - interval_of a] pi))"
        using ci_def pf_pi_def tmf_ivl_cs_length[OF cs_def]
        proof(induction ord arbitrary: cs pi pf ci)
          case (0 cs pi pf)
          from 0(2) obtain c where cs_def: "cs = [c]"
            by (metis Suc_eq_plus1 Suc_length_conv length_0_conv)
          from 0(1) have pi_def: "pi = poly.CN (centered c)\<^sub>p 0 (0)\<^sub>p"
            by (simp add: cs_def)
          show ?case
            by (simp add: 0(1) cs_def pi_def)
        next
          case(Suc n cs pi)
          from Suc(3) obtain c cs' where cs_def: "cs = c # cs'" 
                                   and length_cs': "length cs' = n + 1"
            by (metis Suc_eq_plus1 length_Suc_conv)
          hence "cs' \<noteq> []" by auto
          from cs_def obtain pf' pi' where pf'pi'_def: "(pf', pi') = tmf_polys cs'"
            using prod.collapse by blast
          from Suc(2) have pi_def: "pi = poly.CN (centered c)\<^sub>p 0 pi'"
            by (simp add: cs_def pf'pi'_def[symmetric])
            
          have "set_of (horner_eval (\<lambda>i. interval_map real_of_float (cs ! i) - interval_of (real_of_float (mid (cs ! i)))) (interval_of (x - real_of_float a)) (Suc (Suc n)))
              = set_of (interval_map real_of_float (c) - interval_of (real_of_float (mid c))
                        + interval_of (x - real_of_float a) * horner_eval (\<lambda>i. interval_map real_of_float (cs' !  i) - interval_of (real_of_float (mid (cs' ! i)))) (interval_of (x - real_of_float a)) (Suc n))"
            by (simp add: cs_def)
          also have "... \<subseteq> set_of (interval_map real_of_float c - interval_of (real_of_float (mid c)) + interval_of (x - a) * interval_map real_of_float (Ipoly [I - a] pi'))"
            apply(rule set_of_add_inc_right)
            apply(rule set_of_mul_inc_right)
            by (rule Suc(1)[OF pf'pi'_def length_cs'])
          also have "... \<subseteq> set_of (interval_map real_of_float (Ipoly [I - a] pi))"
            apply(simp add: pi_def)
            apply(rule set_of_add_inc_right)
            apply(rule set_of_mul_inc_left)
            using x_in_I
            by (simp add: set_of_def minus_interval_def uminus_interval_def)
          finally show ?case .
        qed
      finally show ?thesis
        using taylor_expansion
        by (simp add: xs_def)
    qed
    also have "... \<subseteq> set_of (round_ivl prec (Ipoly [I - interval_of a] pi))"
      using real_of_float_round_ivl_correct by auto
    finally show "interpret_floatarith f xs - Ipoly (list_op op- xs (map real_of_float [a])) (pf)
                  \<in> set_of (round_ivl prec (Ipoly [I - interval_of a] pi))"
      .
  next
    show "[a] all_in [I]"
      using \<open>a \<in> set_of I\<close>
      by simp
  qed
qed


subsection \<open>Operations on taylor models\<close>

(* Normalizes the taylor model by transforming its polynomial into horner form.  *)
fun tm_norm_poly :: "taylor_model \<Rightarrow> taylor_model"
where "tm_norm_poly (TaylorModel p e) = TaylorModel (polynate p) e"

(* Reduces the degree of a taylor model's polynomial to n and keeps it valid by increasing the error bound. *)
fun tm_lower_order tm_lower_order_of_normed :: "nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_lower_order ord I a t = tm_lower_order_of_normed ord I a (tm_norm_poly t)"
   |  "tm_lower_order_of_normed ord I a (TaylorModel p e) = (
         let (l, r) = split_by_degree ord p
         in TaylorModel l (e + compute_bound_poly r I a)
       )"

(* We also round our float coefficients. *)
fun tm_round_floats tm_round_floats_of_normed :: "nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_round_floats prec I a t = tm_round_floats_of_normed prec I a (tm_norm_poly t)"
    | "tm_round_floats_of_normed prec I a (TaylorModel p e) = (
         let (l, r) = split_by_prec prec p
         in TaylorModel l (round_ivl prec (e + compute_bound_poly r I a))
       )"

(* Order lowering and rounding on tayor models, also converts the polynomial into horner form. *)
fun tm_norm tm_norm' :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_norm prec ord I a t = tm_norm' prec ord I a (tm_norm_poly t)"
    | "tm_norm' prec ord I a t = tm_round_floats_of_normed prec I a (tm_lower_order_of_normed ord I a t)" 

fun tm_neg :: "taylor_model \<Rightarrow> taylor_model"
where "tm_neg (TaylorModel p e) = TaylorModel (~\<^sub>p p) (-e)"

fun tm_add :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_add (TaylorModel p1 e1) (TaylorModel p2 e2) = TaylorModel (p1 +\<^sub>p p2) (e1 + e2)"

fun tm_sub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_sub t1 t2 = tm_add t1 (tm_neg t2)"

(* Note: This increases the degree of the polynomial. tm_lower_order can be used to reduce it again. *)
fun tm_mul :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_mul prec ord I a (TaylorModel p1 e1) (TaylorModel p2 e2) = (
         let d1 = compute_bound_poly p1 I a;
             d2 = compute_bound_poly p2 I a;
             p = p1 *\<^sub>p p2;
             e = e1*d2 + d1*e2 + e1*e2
         in tm_norm' prec ord I a (TaylorModel p e)
       )"
  
fun tm_pow :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> nat \<Rightarrow> taylor_model"
where "tm_pow prec ord I a t 0 = tm_const 1"
    | "tm_pow prec ord I a t (Suc n) = (
         if odd (Suc n)
         then tm_mul prec ord I a t (tm_pow prec ord I a t n)
         else let t' = tm_pow prec ord I a t ((Suc n) div 2)
              in tm_mul prec ord I a t' t'
       )"

(* Evaluates a float polynomial, using a taylor model as the parameter. This is used to compose taylor models. *)
fun eval_poly_at_tm :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float poly \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "eval_poly_at_tm prec ord I a (poly.C c) t = tm_const c"
    | "eval_poly_at_tm prec ord I a (poly.Bound n) t = t"
    | "eval_poly_at_tm prec ord I a (poly.Add p1 p2) t
         = tm_add (eval_poly_at_tm prec ord I a p1 t)
                  (eval_poly_at_tm prec ord I a p2 t)"
    | "eval_poly_at_tm prec ord I a (poly.Sub p1 p2) t
         = tm_sub (eval_poly_at_tm prec ord I a p1 t)
                  (eval_poly_at_tm prec ord I a p2 t)"
    | "eval_poly_at_tm prec ord I a (poly.Mul p1 p2) t
         = tm_mul prec ord I a (eval_poly_at_tm prec ord I a  p1 t)
                               (eval_poly_at_tm prec ord I a p2 t)"
    | "eval_poly_at_tm prec ord I a (poly.Neg p) t
         = tm_neg (eval_poly_at_tm prec ord I a p t)"
    | "eval_poly_at_tm prec ord I a (poly.Pw p n) t
         = tm_pow prec ord I a (eval_poly_at_tm prec ord I a p t) n"
    | "eval_poly_at_tm prec ord I a (poly.CN c n p) t = (
         let pt = eval_poly_at_tm prec ord I a p t;
             t_mul_pt = tm_mul prec ord I a t pt 
         in tm_add (eval_poly_at_tm prec ord I a c t) t_mul_pt
       )"

fun tm_inc_err :: "float interval \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_inc_err i (TaylorModel p e) = TaylorModel p (e + i)"
    
fun tm_comp :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_comp prec ord I a ta (TaylorModel p e) t = (
         let t_sub_ta = tm_sub t (tm_const ta);
             pt = eval_poly_at_tm prec ord I a p t_sub_ta
         in tm_inc_err e pt
       )"

(* tm_abs, tm_min and tm_max are implemented extremely naively, because I don't expect them to be very useful.
   But the implementation is fairly modular, i.e. tm_{abs,min,max} all can easily be swapped out,
   as long as the corresponding correctness lemmas tm_{abs,min,max}_valid are updated as well. *)
fun tm_abs :: "float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_abs I a t = (
  let bound = compute_bound_tm I a t; abs_bound=Ivl (0::float) (max (abs (lower bound)) (abs (upper bound)))
  in TaylorModel (poly.C (mid abs_bound)) (centered abs_bound))"

fun tm_and :: "float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_and I a t1 t2 = (
  let b1 = compute_bound_tm I a t1; b2 = compute_bound_tm I a t2;
      b_combined = interval_union b1 b2
  in TaylorModel (poly.C (mid b_combined)) (centered b_combined))"
  
fun tm_min :: "float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_min I a t1 t2 = tm_and I a t1 t2"
  
fun tm_max :: "float interval list \<Rightarrow> float list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_max I a t1 t2 = tm_and I a t1 t2"


(* Validity of is preserved by our operations on taylor models. *)
lemma tm_norm_poly_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a f (tm_norm_poly t)"
using assms
apply(cases t)
apply(simp)
using num_params_polynate le_trans
by blast

lemma tm_lower_order_of_normed_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a f (tm_lower_order_of_normed ord I a t)"
proof-
  obtain p e where t_decomp: "t = TaylorModel p e"
    by (cases t) simp
  obtain pl pr where p_split: "split_by_degree ord p = (pl, pr)"
    by (cases "split_by_degree ord p", simp)
  
  show ?thesis
  proof(rule valid_tmI)
    show "tm_lower_order_of_normed ord I a t = TaylorModel pl (e + compute_bound_poly pr I a)"
    by (simp add: t_decomp p_split)
  next
    show "num_params pl \<le> length I"
      using split_by_degree_correct(3)[OF p_split[symmetric]]
            valid_tmD'(1)[OF assms(1) t_decomp]
            num_params_polynate
      using le_trans by blast
  next
    fix x :: "real list" assume "x all_in I"
    
    have num_params_pr: "num_params pr \<le> length I"
      using split_by_degree_correct(4)[OF p_split[symmetric]]
            valid_tmD'(1)[OF assms(1) t_decomp]
            num_params_polynate
      using le_trans by blast
    have "f x - Ipoly (list_op op- x (a::real list)) pl = (f x - Ipoly (list_op op- x (a::real list)) p) + Ipoly (list_op op- x (a::real list)) pr"
      using split_by_degree_correct(2)[OF p_split[symmetric], of "list_op op- x (a::real list)"]
      by simp
    also have "... \<in> set_of (e + compute_bound_poly pr I a)"
      apply(simp)
      apply(rule set_of_add_mono)
      using valid_tmD'(3)[OF assms(1) t_decomp `x all_in I`] 
            compute_bound_poly_correct[OF num_params_pr `x all_in I`] assms(1)
      by auto
    finally show "f x - Ipoly (list_op op- x (a::real list)) pl \<in> set_of (e + compute_bound_poly pr I a)"
      .
  next
    show "a all_in I" using assms(1) by auto
  qed
qed

lemma tm_lower_order_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a f (tm_lower_order ord I a t)"
using assms tm_lower_order_of_normed_valid tm_norm_poly_valid
by simp

lemma tm_round_floats_of_normed_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a f (tm_round_floats_of_normed prec I a t)"
proof-
  obtain p e where t_decomp: "t = TaylorModel p e"
    by (cases t) simp
  obtain pl pr where p_prec: "split_by_prec prec p = (pl, pr)"
    by (cases "split_by_prec prec p", simp)
  
  show ?thesis
  proof(rule valid_tmI)
    show "tm_round_floats_of_normed prec I a t = TaylorModel pl (round_ivl prec (e + compute_bound_poly pr I a))"
    by (simp add: t_decomp p_prec)
  next
    show "num_params pl \<le> length I"
      using split_by_prec_correct(2)[OF p_prec[symmetric]]
            valid_tmD'(1)[OF assms(1) t_decomp]
            num_params_polynate
      using le_trans by blast
  next
    fix x :: "real list" assume "x all_in I"
    
    have num_params_pr: "num_params pr \<le> length I"
      using split_by_prec_correct(3)[OF p_prec[symmetric]]
            valid_tmD'(1)[OF assms(1) t_decomp]
            num_params_polynate
      using le_trans by blast
    have "f x - Ipoly (list_op op- x (a::real list)) pl = (f x - Ipoly (list_op op- x (a::real list)) p) + Ipoly (list_op op- x (a::real list)) pr"
      using split_by_prec_correct(1)[OF p_prec[symmetric], of "list_op op- x (a::real list)"]
      by simp
    also have "... \<in> set_of (e + compute_bound_poly pr I a)"
      apply(simp)
      apply(rule set_of_add_mono)
      using valid_tmD'(3)[OF assms(1) t_decomp `x all_in I`] 
            compute_bound_poly_correct[OF num_params_pr `x all_in I`] assms(1)
      by auto
    also have "... \<subseteq> set_of (round_ivl prec (e + compute_bound_poly pr I a))"
      by(rule real_of_float_round_ivl_correct)
    finally show "f x - Ipoly (list_op op- x (a::real list)) pl \<in> set_of (round_ivl prec (e + compute_bound_poly pr I a))"
      .
  next
    show "a all_in I" using assms(1) by auto
  qed
qed

lemma tm_round_floats_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a f (tm_round_floats prec I a t)"
using assms tm_round_floats_of_normed_valid tm_norm_poly_valid
by simp

lemma tm_norm'_valid:
assumes "valid_tm I a f t" 
shows "valid_tm I a f (tm_norm' prec ord I a t)"
using tm_round_floats_of_normed_valid[OF tm_lower_order_of_normed_valid[OF assms]]
by simp

lemma tm_norm_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a f (tm_norm prec ord I a t)"
using assms tm_norm'_valid tm_norm_poly_valid
by simp

lemma tm_neg_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a (-f) (tm_neg t)"
proof-
  from valid_tmD[OF assms]
  obtain p e where t_def: 
    "t = TaylorModel p e"
    "num_params p \<le> length I"
    "a all_in I"
    "\<And>x::real list. x all_in I \<Longrightarrow> f x - Ipoly (list_op op- x (a::real list)) p \<in> set_of e"
      by auto
  show ?thesis
    proof(rule valid_tmI)
      show "tm_neg t = TaylorModel (~\<^sub>p p) (-e)"
        by (simp add: t_def(1) uminus_interval_def)
    next
      show "num_params (~\<^sub>p p) \<le> length I"
        using t_def(2)
        by (simp add: num_params_polyneg)
    next
      show "a all_in I"
        using assms by auto
    next
      fix x::"real list" assume assms: "x all_in I"
      show "(- f) x - Ipoly (list_op op- x (a::real list)) (~\<^sub>p p) \<in> set_of (-e)"
        using t_def(4)[OF assms]
        apply(simp add: poly_map_real_polyneg)
        using set_of_uminus_mono
        by fastforce
    qed
qed

lemma tm_add_valid:
assumes "valid_tm I a f t1"
assumes "valid_tm I a g t2"
shows "valid_tm I a (f + g) (tm_add t1 t2)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 e1 where t1_def:
    "t1 = TaylorModel p1 e1"
    "num_params p1 \<le> length I"
    "a all_in I"
    "\<And>x::real list. x all_in I \<Longrightarrow> f x - Ipoly (list_op op- x (a::real list)) p1 \<in> set_of e1"
      by auto
  from valid_tmD[OF assms(2)]
  obtain p2 e2 where t2_def:
    "t2 = TaylorModel p2 e2"
    "num_params p2 \<le> length I"
    "a all_in I"
    "\<And>x::real list. x all_in I \<Longrightarrow> g x - Ipoly (list_op op- x (a::real list)) p2 \<in> set_of e2"
      by auto
   
  show "valid_tm I a (f + g) (tm_add t1 t2)"
    proof(rule valid_tmI[OF _ _ \<open>a all_in I\<close>])
      show "tm_add t1 t2 = TaylorModel (p1 +\<^sub>p p2) (Ivl (lower e1 + lower e2) (upper e1 + upper e2))"
        by (simp add: t1_def(1) t2_def(1) plus_interval_def)
    next
      show "num_params (p1 +\<^sub>p p2) \<le> length I"
      using num_params_polyadd[of p1 p2] t1_def(2) t2_def(2)
      by simp
    next
      fix x::"real list" assume assms: "x all_in I"
      from t1_def(4)[OF this] t2_def(4)[OF this]
      show "(f + g) x - Ipoly (list_op op- x (a::real list)) (p1 +\<^sub>p p2) \<in> set_of ((Ivl (lower e1 + lower e2) (upper e1 + upper e2)))"
        by (simp add: poly_map_real_polyadd set_of_def interval_map_def)
    qed
qed

lemma tm_sub_valid:
assumes "valid_tm I a f t1"
assumes "valid_tm I a g t2"
shows "valid_tm I a (f - g) (tm_sub t1 t2)"
using tm_add_valid[OF assms(1) tm_neg_valid[OF assms(2)]]
by simp

lemma tm_mul_valid:
assumes "valid_tm I a f t1"
assumes "valid_tm I a g t2"
shows "valid_tm I a (f * g) (tm_mul prec ord I a t1 t2)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 i1 where t1_def:
    "t1 = TaylorModel p1 i1"
    "num_params p1 \<le> length I"
    "a all_in I"
    "\<And>x::real list. x all_in I \<Longrightarrow> f x - Ipoly (list_op op- x (a::real list)) p1 \<in> set_of i1"
      by blast
  from valid_tmD[OF assms(2)]
  obtain p2 i2 where t2_def:
    "t2 = TaylorModel p2 i2"
    "num_params p2 \<le> length I"
    "a all_in I"
    "\<And>x::real list. x all_in I \<Longrightarrow> g x - Ipoly (list_op op- x (a::real list)) p2 \<in> set_of i2"
      by blast
      
  show "valid_tm I a (f * g) (tm_mul prec ord I a t1 t2)"
    unfolding t1_def t2_def tm_mul.simps Let_def
    apply(rule tm_norm'_valid)
    apply(rule valid_tmI[OF _ _ \<open>a all_in I\<close>])
    unfolding taylor_model.inject
    apply(rule conjI[OF refl refl])
    defer
    using t1_def(3) t2_def(3)
    proof(goal_cases)
      case (1 x)
      
      let ?x_minus_a="(list_op op- x (a::real list))"
      
      obtain d1 :: real where d1_def: "d1 \<in> set_of i1" "f x - Ipoly ?x_minus_a p1 = d1"
        using t1_def(4)[OF 1(1)] by auto
      obtain d2 :: real where d2_def: "d2 \<in> set_of i2" "g x - Ipoly ?x_minus_a p2 = d2"
        using t2_def(4)[OF 1(1)] by auto
      
      have "(f * g) x = f x * g x"
        by auto
      also have "... = (d1 + Ipoly ?x_minus_a p1) * (d2 + Ipoly ?x_minus_a p2)"
        by (simp add: d1_def(2)[symmetric] d2_def(2)[symmetric])
      also have "... = Ipoly ?x_minus_a p1 * Ipoly ?x_minus_a p2 + d1 * Ipoly ?x_minus_a p2 + Ipoly ?x_minus_a p1 * d2 + d1 * d2"
        by (simp add: algebra_simps)
      finally have f_times_g_eq: "(f * g) x - Ipoly ?x_minus_a p1 * Ipoly ?x_minus_a p2 = d1 * Ipoly ?x_minus_a p2 + Ipoly ?x_minus_a p1 * d2 + d1 * d2"
        by simp
      also have "... \<in> set_of (i1 * compute_bound_poly p2 I a) +  set_of (compute_bound_poly p1 I a * i2) + set_of (i1 * i2)"
        apply(rule set_plus_intro[OF set_plus_intro])
        using d1_def(1) d2_def(1) compute_bound_poly_correct[OF t1_def(2) 1(1) `a all_in I`] compute_bound_poly_correct[OF t2_def(2) 1(1) `a all_in I`]
        by (simp_all add: set_of_mult_mono)
      also have "... = set_of (i1 * compute_bound_poly p2 I a + compute_bound_poly p1 I a * i2 + i1 * i2)"
        by (simp add: t1_def(2) t2_def(2) set_of_add_distrib)
      finally have "(f * g) x - Ipoly ?x_minus_a p1 * Ipoly ?x_minus_a p2  \<in> set_of (i1 * compute_bound_poly p2 I a + compute_bound_poly p1 I a * i2 + i1 * i2)"
        .
      thus ?case
        by (simp add: poly_map_real_polymul)
    next
      case 2
      show ?case
        using t1_def(2) t2_def(2) num_params_polymul[of p1 p2]
        by simp
    qed
qed

lemma tm_pow_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a (f ^ n) (tm_pow prec ord I a t n)"
using assms
proof(induction n arbitrary: t rule: tm_pow.induct)
  case (1 pr ord I a t t')
  thus ?case
    apply(simp)
    using all_in_def
    by auto
next
  case (2 pr ord I a t n t')
  show ?case
  proof(cases)
    assume "odd (Suc n)"
    show ?thesis
      unfolding tm_pow.simps if_P[OF \<open>odd (Suc n)\<close>] power_Suc
      by (rule tm_mul_valid[OF 2(3) 2(1)[OF \<open>odd (Suc n)\<close> 2(3)]])
  next
    assume "\<not>odd (Suc n)"
    hence "even (Suc n)"
      by simp
    have f_pow_n_decomp: "f^(Suc n) = f^(Suc n div 2) * f^(Suc n div 2)"
      apply(subst even_two_times_div_two[OF \<open>even (Suc n)\<close>, symmetric])
      unfolding semiring_normalization_rules(36)
      by simp
    show ?thesis
      unfolding tm_pow.simps if_not_P[OF \<open>\<not>odd (Suc n)\<close>] f_pow_n_decomp Let_def
      apply(rule tm_mul_valid)
      using 2(2)[OF \<open>\<not>odd (Suc n)\<close> 2(3)]
      by simp_all
  qed
qed

lemma eval_poly_at_tm_valid:
assumes "num_params p \<le> 1"
assumes tg_def: "valid_tm I a g tg"
shows "valid_tm I a ((\<lambda>x. Ipoly ([x]) p) o g) (eval_poly_at_tm prec ord I a p tg)"
using assms(1)
proof(induction p)
  case (C c) thus ?case
    using tg_def
    by auto
next
  case (Bound n) thus ?case
    using tg_def
    by simp
next
  case (Add p1l p1r) thus ?case 
    using tm_add_valid by (simp add: func_plus)
next
  case (Sub p1l p1r) thus ?case 
    using tm_sub_valid by (simp add: fun_diff_def)
next
  case (Mul p1l p1r) thus ?case 
    using tm_mul_valid[OF _ _] by (simp add: func_times)
next
  case (Neg p1') thus ?case 
    using tm_neg_valid by (simp add: fun_Compl_def)
next
  case (Pw p1' n) thus ?case 
    using tm_pow_valid[OF _ ] by (simp add: fun_pow)
next
  case (CN p1l n p1r) thus ?case 
    using tm_add_valid[OF _ tm_mul_valid[OF _ _ ], unfolded func_plus func_times] tg_def by simp
qed
        
lemma tm_comp_valid:
assumes gI_def: "\<And>x. x all_in I \<Longrightarrow> g x \<in> set_of gI"
assumes tf_def: "valid_tm [gI] [ga] (\<lambda>x. f (x ! 0)) tf"
assumes tg_def: "valid_tm I a g tg"
shows "valid_tm I a (f o g) (tm_comp prec ord I a ga tf tg)"
proof-
  obtain pf ef where tf_decomp: "tf = TaylorModel pf ef" using taylor_model.exhaust by auto
  obtain pg eg where tg_decomp: "tg = TaylorModel pg eg" using taylor_model.exhaust by auto
  
  from valid_tmD'[OF tf_def tf_decomp] have tf_valid:
    "num_params pf \<le> 1"
    "ga \<in> set_of gI"
    "\<And>x::real list. x all_in [gI::real interval] \<Longrightarrow> f (x ! 0) - Ipoly (list_op op- x [ga]) pf \<in> set_of (ef::real interval)"
      by (simp_all)
  {
    fix x::"real list"
    assume "x all_in I"
    from tf_valid(3)[of "[g x]", simplified, OF gI_def[OF this]]
    have "f (g x) - Ipoly [g x - ga] pf \<in> set_of ef"
      by simp
  }
  note tf_g_valid = this
      
  from valid_tmD'[OF tg_def tg_decomp] have tg_valid:
    "num_params pg \<le> length I"
    "a all_in I"
    "\<And>x::real list. x all_in I \<Longrightarrow> g x - Ipoly (list_op op- x (a::real list)) pg \<in> set_of eg"
      by simp_all
      
  obtain p' e' where p'e'_def: "TaylorModel p' e' = eval_poly_at_tm prec ord I a pf (tm_sub tg (tm_const ga))"
    using taylor_model.exhaust by smt
  
  have "valid_tm I a (\<lambda>x. g x - ga) (tm_sub tg (tm_const ga))"
    using tm_sub_valid[OF tg_def tm_const_valid[OF \<open>a all_in I\<close>, of ga]]
    by auto
  from eval_poly_at_tm_valid[OF tf_valid(1) this]
  have "valid_tm I a ((\<lambda>x. Ipoly ([x - ga]) pf) o g) (eval_poly_at_tm prec ord I a pf (tm_sub tg (tm_const ga)))"
    by (simp add: comp_def)
  from valid_tmD'[OF this p'e'_def[symmetric]]
  have eval_poly_at_tm_valid:
    "num_params p' \<le> length I"
    "\<And>x. x all_in map (interval_map real_of_float) I \<Longrightarrow>
  ((\<lambda>x. Ipoly [x - real_of_float ga] (poly_map real_of_float pf)) \<circ> g) x -
  Ipoly (list_op op- x (map real_of_float a)) (poly_map real_of_float p')
  \<in> set_of (interval_map real_of_float e')"
      by auto
  show ?thesis
    proof(rule valid_tmI)
      show "tm_comp prec ord I a ga tf tg = TaylorModel p' (e'+ef)"
        using p'e'_def[symmetric]
        by (simp add: tf_decomp)
    next
      show "num_params p' \<le> length I"
        by (simp add: eval_poly_at_tm_valid(1))
    next
      show "a all_in I" using tg_valid(2) by simp
    next
      fix x :: "real list" assume "x all_in I"
      
      have "Ipoly [g x - ga] pf - Ipoly (list_op op- x (a::real list)) p' \<in> set_of e'"
        using eval_poly_at_tm_valid(2)[OF \<open>x all_in I\<close>]
        by simp
      thus "(f \<circ> g) x - Ipoly (list_op op- x (a::real list)) p' \<in> set_of (e' + ef)"
        using set_of_add_mono tf_g_valid[OF \<open>x all_in I\<close>]
        by force
    qed
qed

lemma tm_abs_valid:
assumes "valid_tm I a f t"
shows "valid_tm I a (abs o f) (tm_abs I a t)"
proof-
  obtain p e where t_def[simp]: "t = TaylorModel p e" using taylor_model.exhaust by auto
  def bound\<equiv>"compute_bound_tm I a (TaylorModel p e)"
  def abs_bound\<equiv>"Ivl 0 (max \<bar>lower bound\<bar> \<bar>upper bound\<bar>)"
  have tm_abs_decomp: "tm_abs I a t =  TaylorModel (poly.C (mid abs_bound)) (centered abs_bound)"
    by (simp add: bound_def abs_bound_def Let_def)
  show ?thesis
    apply(rule valid_tmI[OF tm_abs_decomp])
    apply(simp)
    using assms 
    apply(simp)
    proof(goal_cases)
      case (1 x)
      from compute_bound_tm_correct[OF assms this, unfolded t_def bound_def[symmetric]]
      show ?case
        using abs_bound_def real_of_float_max  
        by (auto simp: set_of_def interval_map_def minus_interval_def)
    qed
qed

lemma tm_and_valid_left:
assumes "valid_tm I a f t1"
shows "valid_tm I a f (tm_and I a t1 t2)"
proof-
  def b1\<equiv>"compute_bound_tm I a t1"
  def b2\<equiv>"compute_bound_tm I a t2"
  def b_combined\<equiv>"Ivl (min (lower b1) (lower b2)) (max (upper b1) (upper b2))"

  obtain p e where tm_and_decomp: "tm_and I a t1 t2 = TaylorModel p e"
    using taylor_model.exhaust by auto
  then have p_def: "p = (mid b_combined)\<^sub>p"
        and e_def: "e = centered b_combined"
    by (auto simp: Let_def b1_def b2_def b_combined_def interval_union_def)
  
  show ?thesis
    apply(rule valid_tmI[OF tm_and_decomp])
    apply(simp add: p_def)
    using assms
    apply(auto)[1]
    apply(drule compute_bound_tm_correct[OF assms])
    apply(simp add: set_of_def e_def p_def b_combined_def b1_def)
    apply(safe)
    by (simp_all add: interval_map_def minus_interval_def real_of_float_max real_of_float_min)
qed

lemma tm_and_valid_right:
assumes "valid_tm I a g t2"
shows "valid_tm I a g (tm_and I a t1 t2)"
using tm_and_valid_left[OF assms]
by (simp add: interval_union_commute)

lemma tm_min_valid:
assumes "valid_tm I a f t1"
assumes "valid_tm I a g t2"
shows "valid_tm I a (\<lambda>x. min (f x) (g x)) (tm_min I a t1 t2)"
proof-
  obtain p e where tm_and_decomp: "tm_and I a t1 t2 = TaylorModel p e"
    using taylor_model.exhaust by auto
  
  note a = valid_tmD'[OF tm_and_valid_left[OF assms(1)] tm_and_decomp]
  note b = valid_tmD'[OF tm_and_valid_right[OF assms(2)] tm_and_decomp]
  
  show ?thesis
  unfolding tm_min.simps
  proof(rule valid_tmI[OF tm_and_decomp a(1,2)])
    fix x::"real list" assume "x all_in I"
    from a(3)[OF this] b(3)[OF this]
    show "min (f x) (g x) - Ipoly (list_op op- x (a::real list)) p \<in> set_of e"
      by (cases "f x \<le> g x", simp_all add: min_def)
  qed
qed

lemma tm_max_valid:
assumes "valid_tm I a f t1"
assumes "valid_tm I a g t2"
shows "valid_tm I a (\<lambda>x. max (f x) (g x)) (tm_max I a t1 t2)"
proof-
  obtain p e where tm_and_decomp: "tm_and I a t1 t2 = TaylorModel p e"
    using taylor_model.exhaust by auto
  
  note a = valid_tmD'[OF tm_and_valid_left[OF assms(1)] tm_and_decomp]
  note b = valid_tmD'[OF tm_and_valid_right[OF assms(2)] tm_and_decomp]
  
  show ?thesis
  unfolding tm_max.simps
  proof(rule valid_tmI[OF tm_and_decomp a(1,2)])
    fix x::"real list" assume "x all_in I"
    from a(3)[OF this] b(3)[OF this]
    show "max (f x) (g x) - Ipoly (list_op op- x (a::real list)) p \<in> set_of e"
      by (cases "f x \<le> g x", simp_all add: max_def)
  qed
qed


subsection \<open>Computing taylor models for multivariate expressions\<close>

(* Compute taylor models for expressions of the form "f (g x)", where f is an elementary function like exp or cos,
   by composing taylor models for f and g. For our correctness proof, we need to make it explicit that the range
   of g on I is inside the domain of f, by introducing the f_exists_on predicate. *)
fun compute_tm_by_comp :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> taylor_model option \<Rightarrow> (float interval \<Rightarrow> bool) \<Rightarrow> taylor_model option"
where "compute_tm_by_comp prec ord I a f g f_exists_on = (
         case g
         of Some tg \<Rightarrow> (
           let gI = compute_bound_tm I a tg;
               ga = mid (compute_bound_tm a a tg)
           in if f_exists_on gI
              then map_option (\<lambda>tf. tm_comp prec ord I a ga tf tg ) (tm_floatarith prec ord gI ga f)
              else None)
         | _ \<Rightarrow> None
       )"

(* Compute taylor models of degree n from floatarith expressions. *)
fun compute_tm :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "compute_tm _ _ I _ (Num c) = Some (tm_const c)"
    | "compute_tm _ _ I a (Var n) = Some (tm_var n a)"
    | "compute_tm prec ord I a (Add l r) = (
         case (compute_tm prec ord I a l, compute_tm prec ord I a r) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_add t1 t2)
          | _ \<Rightarrow> None)"
    | "compute_tm prec ord I a (Minus f)
         = map_option tm_neg (compute_tm prec ord I a f)"
    | "compute_tm prec ord I a (Mult l r) = (
         case (compute_tm prec ord I a l, compute_tm prec ord I a r) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_mul prec ord I a t1 t2)
          | _ \<Rightarrow> None)"     
    | "compute_tm prec ord I a (Power f k)
         = map_option (\<lambda>t. tm_pow prec ord I a t k)
                      (compute_tm prec ord I a f)"
    | "compute_tm prec ord I a (Inverse f)
         = compute_tm_by_comp prec ord I a (Inverse (Var 0)) (compute_tm prec ord I a f) (\<lambda>x. 0 < lower x \<or> upper x < 0)"
    | "compute_tm prec ord I a (Cos f)
         = compute_tm_by_comp prec ord I a (Cos (Var 0)) (compute_tm prec ord I a f) (\<lambda>x. True)"
    | "compute_tm prec ord I a (Arctan f)
         = compute_tm_by_comp prec ord I a (Arctan (Var 0)) (compute_tm prec ord I a f) (\<lambda>x. True)"
    | "compute_tm prec ord I a (Exp f)
         = compute_tm_by_comp prec ord I a (Exp (Var 0)) (compute_tm prec ord I a f) (\<lambda>x. True)"
    | "compute_tm prec ord I a (Ln f)
         = compute_tm_by_comp prec ord I a (Ln (Var 0)) (compute_tm prec ord I a f) (\<lambda>x. 0 < lower x)"
    | "compute_tm prec ord I a (Sqrt f)
         = compute_tm_by_comp prec ord I a (Sqrt (Var 0)) (compute_tm prec ord I a f) (\<lambda>x. 0 < lower x)"
    | "compute_tm prec ord I a Pi = Some (tm_pi prec)"
    | "compute_tm prec ord I a (Abs f)
         = map_option (tm_abs I a) (compute_tm prec ord I a f)"
    | "compute_tm prec ord I a (Min l r) = (
         case (compute_tm prec ord I a l, compute_tm prec ord I a r) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_min I a t1 t2)
          | _ \<Rightarrow> None)"
    | "compute_tm prec ord I a (Max l r) = (
         case (compute_tm prec ord I a l, compute_tm prec ord I a r) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_max I a t1 t2)
          | _ \<Rightarrow> None)"

lemma compute_tm_by_comp_valid:
assumes "num_vars f \<le> 1"
assumes tx_valid: "valid_tm I a (interpret_floatarith g) tg"
assumes t_def: "Some t = compute_tm_by_comp prec ord I a f (Some tg) c"
assumes f_deriv: "\<And>x. x \<in> set_of (interval_map real_of_float (compute_bound_tm I a tg)) \<Longrightarrow> c (compute_bound_tm I a tg) \<Longrightarrow> isDERIV 0 f [x]"
shows "valid_tm I a ((\<lambda>x. interpret_floatarith f [x]) o interpret_floatarith g) t"
proof-
  from t_def[simplified, simplified Let_def]
  obtain tf
  where t1_def: "Some tf = tm_floatarith prec ord (compute_bound_tm I a tg) (mid (compute_bound_tm (map interval_of a) a tg)) f"
  and t_decomp: "t = tm_comp prec ord I a (mid (compute_bound_tm (map interval_of a) a tg)) tf tg "
  and c_true:   "c (compute_bound_tm I a tg)"
    unfolding Let_def
    by (smt option.collapse option.distinct(1) option.map_sel option.sel option.simps(8))
  have a1: "mid (compute_bound_tm (map interval_of a) a tg) \<in> set_of (compute_bound_tm I a tg)"
    apply(rule rev_subsetD[OF mid_in_interval compute_bound_tm_mono[OF valid_tm_subset[OF _ _ tx_valid]]])
    using tx_valid
    by (auto simp add: set_of_def)
  from \<open>num_vars f \<le> 1\<close>
  have [simp]: "\<And>x. 0 \<le> length x \<Longrightarrow> (\<lambda>x. interpret_floatarith f [x ! 0]) x = interpret_floatarith f x"
    by (induction f, simp_all)
  show ?thesis
    unfolding t_decomp
    apply(rule tm_comp_valid[OF _ _ tx_valid])
    apply(rule compute_bound_tm_correct[OF tx_valid])
    apply(simp)
    using tm_floatarith_valid[OF a1 f_deriv[OF _ c_true] t1_def, simplified]
    by simp
qed

lemma compute_tm_valid:
assumes num_vars_f: "num_vars f \<le> length I"
assumes "a all_in I"
assumes t_def: "Some t = compute_tm prec ord I a f"
shows "valid_tm I a (interpret_floatarith f) t"
using num_vars_f t_def
proof(induct f arbitrary: t)
  case (Var n)
  thus ?case
    using assms(2) by simp
next
  case (Num c)
  thus ?case 
    using assms(2) by (simp add: assms(3))
next
  case (Add l r t)
  obtain t1 where t1_def: "Some t1 = compute_tm prec ord I a l"
    by (metis (no_types, lifting) Add(4) compute_tm.simps(3) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "Some t2 = compute_tm prec ord I a r"
    by (smt Add(4) compute_tm.simps(3) option.case_eq_if option.collapse prod.case)
  have t_def: "t = tm_add t1 t2"
    using Add(4) t1_def t2_def
    by (metis compute_tm.simps(3) option.case(2) option.inject prod.case)
  
  have [simp]: "interpret_floatarith (floatarith.Add l r) = interpret_floatarith l + interpret_floatarith r"
    by auto
  show "valid_tm I a (interpret_floatarith (floatarith.Add l r)) t"
    apply(simp add: t_def)
    apply(rule tm_add_valid[OF Add(1)[OF _ t1_def] Add(2)[OF _ t2_def]])
    using Add(3) by auto
next
  case (Minus f t)
  have [simp]: "interpret_floatarith (Minus f) = -interpret_floatarith f"
    by auto
   
  obtain t1 where t1_def: "Some t1 = compute_tm prec ord I a f"
    by (metis Minus.prems(2) compute_tm.simps(4) map_option_eq_Some)
  have t_def: "t = tm_neg t1"
    by (metis Minus.prems(2) compute_tm.simps(4) option.inject option.simps(9) t1_def)
  
  show "valid_tm I a (interpret_floatarith (Minus f)) t"
    apply(simp add: t_def, rule tm_neg_valid[OF Minus(1)[OF _ t1_def]])
    using Minus(2) by auto
next
  case (Mult l r t)
  obtain t1 where t1_def: "Some t1 = compute_tm prec ord I a l"
    by (metis (no_types, lifting) Mult(4) compute_tm.simps(5) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "Some t2 = compute_tm prec ord I a r"
    by (smt Mult(4) compute_tm.simps(5) option.case_eq_if option.collapse prod.case)
  have t_def: "t = tm_mul prec ord I a t1 t2"
    using Mult(4) t1_def t2_def
    by (metis compute_tm.simps(5) option.case(2) option.inject prod.case)
  
  have [simp]: "interpret_floatarith (floatarith.Mult l r) = interpret_floatarith l * interpret_floatarith r"
    by auto
  show "valid_tm I a (interpret_floatarith (floatarith.Mult l r)) t"
    apply(simp add: t_def)
    apply(rule tm_mul_valid[OF Mult(1)[OF _ t1_def] Mult(2)[OF _ t2_def]])
    using Mult(3) by auto
next
  case (Power f k t)
  from Power(3)
  obtain tm_f where tm_f_def: "Some tm_f =  compute_tm prec ord I a f"
    apply(simp) using map_option_eq_Some by metis
  have t_decomp: "t = tm_pow prec ord I a tm_f k"
    using Power(3) by (simp add: tm_f_def[symmetric])
  show ?case
    using tm_pow_valid[OF Power(1)[OF Power(2)[simplified] tm_f_def]]
    by (simp add: t_decomp fun_pow)
next
  case (Inverse f t)
  from Inverse(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse)
  have "\<And>x. x \<in> set_of (interval_map real_of_float (compute_bound_tm I a tf)) \<Longrightarrow>
          0 < lower (compute_bound_tm I a tf) \<or> upper (compute_bound_tm I a tf) < 0 \<Longrightarrow>
          isDERIV 0 (Inverse (Var 0)) [x]"
    by (simp add: set_of_def interval_map_def, safe, simp_all)
  thus ?case
    using compute_tm_by_comp_valid[OF _ Inverse(1)[OF Inverse(2)[simplified] tf_def] Inverse(3)[unfolded compute_tm.simps tf_def[symmetric]]]
    by (cases t, simp)
next
  case (Cos f t)
  from Cos(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse)
  show ?case
    using compute_tm_by_comp_valid[OF _ Cos(1)[OF Cos(2)[simplified] tf_def] Cos(3)[unfolded compute_tm.simps tf_def[symmetric]]]
    by (cases t, simp)
next
  case (Arctan f t)
  from Arctan(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse)
  show ?case
    using compute_tm_by_comp_valid[OF _ Arctan(1)[OF Arctan(2)[simplified] tf_def] Arctan(3)[unfolded compute_tm.simps tf_def[symmetric]]]
    by (cases t, simp)
next
  case (Exp f t)
  from Exp(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse)
  show ?case
    using compute_tm_by_comp_valid[OF _ Exp(1)[OF Exp(2)[simplified] tf_def] Exp(3)[unfolded compute_tm.simps tf_def[symmetric]]]
    by (cases t, simp)
next
  case (Ln f t)
  from Ln(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse)
  have "\<And>x. x \<in> set_of (interval_map real_of_float (compute_bound_tm I a tf)) \<Longrightarrow>
          0 < lower (compute_bound_tm I a tf) \<Longrightarrow>
          isDERIV 0 (Ln (Var 0)) [x]"
    by (simp add: set_of_def interval_map_def)
  thus ?case
    using compute_tm_by_comp_valid[OF _ Ln(1)[OF Ln(2)[simplified] tf_def] Ln(3)[unfolded compute_tm.simps tf_def[symmetric]]]
    by (cases t, simp)
next
  case (Sqrt f t)
  from Sqrt(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse)
  have "\<And>x. x \<in> set_of (interval_map real_of_float (compute_bound_tm I a tf)) \<Longrightarrow>
          0 < lower (compute_bound_tm I a tf) \<Longrightarrow>
          isDERIV 0 (Sqrt (Var 0)) [x]"
    by (simp add: set_of_def interval_map_def)
  thus ?case
    using compute_tm_by_comp_valid[OF _ Sqrt(1)[OF Sqrt(2)[simplified] tf_def] Sqrt(3)[unfolded compute_tm.simps tf_def[symmetric]]]
    by (cases t, simp)
next
  case (Pi t)
  hence "t = tm_pi prec" by simp
  show ?case
    unfolding `t = tm_pi prec`
    by (rule tm_pi_valid[OF \<open>a all_in I\<close>])
next
  case (Abs f t)
  from Abs(3) obtain tf where tf_def: "Some tf = compute_tm prec ord I a f"
                        and  t_def: "t = tm_abs I a tf"
    by (metis (no_types, lifting) compute_tm.simps(14) map_option_eq_Some)
  from tm_abs_valid[OF Abs(1)[OF Abs(2)[simplified] tf_def]]
  show ?case
     unfolding t_def interpret_floatarith.simps(9) comp_def
     by assumption
next
  case (Min l r t)
  from Min(4)
  obtain t1 t2 where t_decomp:
    "t = tm_min I a t1 t2" and "Some t1 = compute_tm prec ord I a l" and "Some t2 = compute_tm prec ord I a r"
    by (smt compute_tm.simps(15) option.case_eq_if option.collapse option.distinct(2) option.inject split_conv)
  from this(2,3) Min(1-3)
  have t1_valid: "valid_tm I a (interpret_floatarith l) t1"
  and  t2_valid: "valid_tm I a (interpret_floatarith r) t2"
    by auto

  have [simp]: "interpret_floatarith (floatarith.Min l r) = (\<lambda>vs. min (interpret_floatarith l vs) (interpret_floatarith r vs))"
    by auto
    
  show "valid_tm I a (interpret_floatarith (floatarith.Min l r)) t"
    unfolding t_decomp(1)
    apply(simp del: tm_min.simps)
    using t1_valid t2_valid
    by (rule tm_min_valid)
next
  case (Max l r t)
  from Max(4)
  obtain t1 t2 where t_decomp:
    "t = tm_max I a t1 t2" and "Some t1 = compute_tm prec ord I a l" and "Some t2 = compute_tm prec ord I a r"
    by (smt compute_tm.simps(16) option.case_eq_if option.collapse option.distinct(2) option.inject split_conv)
  from this(2,3) Max(1-3)
  have t1_valid: "valid_tm I a (interpret_floatarith l) t1"
  and  t2_valid: "valid_tm I a (interpret_floatarith r) t2"
    by auto

  have [simp]: "interpret_floatarith (floatarith.Max l r) = (\<lambda>vs. max (interpret_floatarith l vs) (interpret_floatarith r vs))"
    by auto
    
  show "valid_tm I a (interpret_floatarith (floatarith.Max l r)) t"
    unfolding t_decomp(1)
    apply(simp del: tm_max.simps)
    using t1_valid t2_valid
    by (rule tm_max_valid)
qed


subsection \<open>Computing bounds for floatarith expressions\<close>

(* Automatically find interval bounds for floatarith expressions. *)
fun compute_ivl_bound :: "nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_ivl_bound prec ord f I = (
         map_option (\<lambda>t. round_ivl prec (compute_bound_tm I (map mid I) t)) (compute_tm prec ord I (map mid I) f)
       )"

fun compute_ivl_bound_subdiv :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_ivl_bound_subdiv prec ord n f I = (
         let Ds = split_domain (subdivide_interval n) I;
             S = those (map (compute_ivl_bound prec ord f) Ds)
         in map_option interval_list_union S
       )"

(* Compute bounds using plain interval arithmetic by subdivision. *)
fun compute_ivl_bound_naive :: "nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_ivl_bound_naive prec n f I = (
         let Ds = split_domain (subdivide_interval n) I;
             S = those (map (compute_bound_fa prec f) Ds)
         in map_option interval_list_union S
       )"

(* Automatically computed bounds are correct. *)
lemma compute_ivl_bound_correct:
assumes "num_vars f \<le> length I"
assumes "Some B = compute_ivl_bound prec ord f I"
assumes "x all_in I"
shows "interpret_floatarith f x \<in> set_of B"
proof-
  from assms(2) obtain t where B_def: "B = round_ivl prec (compute_bound_tm I (map mid I) t)" 
                           and t_def: "Some t = compute_tm prec ord I (map mid I) f"
    by (smt compute_ivl_bound.simps map_option_eq_Some option.simps(8))
  
  from compute_bound_tm_correct[OF compute_tm_valid[OF assms(1) _ t_def] `x all_in I`] mid_in_interval
  show ?thesis
    using real_of_float_round_ivl_correct by (auto simp add: B_def)
qed

lemma compute_ivl_bound_subdiv_correct:
assumes "num_vars f \<le> length I"
assumes "Some B = compute_ivl_bound_subdiv prec ord n f I"
assumes "x all_in I"
shows "interpret_floatarith f x \<in> set_of B"
proof-
  def Ds \<equiv>"split_domain (subdivide_interval n) I"

  have "list_ex (\<lambda>s. x all_in (s:: float interval list)) Ds"
    unfolding Ds_def
    apply(rule split_domain_correct[OF \<open>x all_in I\<close>])
    apply(simp_all add: mid_in_interval)
    apply(drule subdivide_interval_correct)
    by assumption
  then obtain i where i1: "i < length Ds"
             and i2: "x all_in (Ds ! i)"
    by (auto simp: Ds_def list_ex_length)
  obtain S where S_def: "those (map (\<lambda>S. compute_ivl_bound prec ord f S) Ds) = Some S"
    using assms(2) Ds_def
    by fastforce
  have "S \<noteq> []"
    using Some_those_length[OF S_def[symmetric]] i1
    by auto
  moreover have "B = interval_list_union S"
    using assms(2) S_def
    by (simp add: Ds_def[symmetric])
  ultimately have Si_subset_B: "\<And>i. i < length S \<Longrightarrow> set_of (S ! i) \<subseteq> set_of B"
     using interval_list_union_correct
     by auto
  
  have "i < length S"
    using Some_those_length[OF S_def[symmetric]] i1
    by simp
  from Some_those_nth[OF S_def[symmetric] this]
  have SomeSi: "Some (S ! i) = compute_ivl_bound prec ord f (Ds ! i)"
    by (simp add: i1)
  
  from Si_subset_B[OF \<open>i < length S\<close>]
  have "set_of (S ! i) \<subseteq> set_of (B::real interval)"
    by (simp add: interval_map_def set_of_def)
  thus ?thesis
    apply(rule subsetD)
    apply(rule compute_ivl_bound_correct[OF _ SomeSi i2])
    using assms(1) assms(3) i2
    by auto
qed

lemma compute_ivl_bound_naive_correct:
assumes "num_vars f \<le> length I"
assumes "Some B = compute_ivl_bound_naive prec n f I"
assumes "x all_in I"
shows "interpret_floatarith f x \<in> set_of B"
proof-
  def Ds \<equiv>"split_domain (subdivide_interval n) I"

  have "list_ex (\<lambda>s. x all_in (s:: float interval list)) Ds"
    unfolding Ds_def
    apply(rule split_domain_correct[OF \<open>x all_in I\<close>])
    apply(simp_all add: mid_in_interval)
    apply(drule subdivide_interval_correct)
    by assumption
  then obtain i where i1: "i < length Ds"
             and i2: "x all_in (Ds ! i)"
    by (auto simp: Ds_def list_ex_length)
  obtain S where S_def: "those (map (\<lambda>S. compute_bound_fa prec f S) Ds) = Some S"
    using assms(2) Ds_def
    by fastforce
  have "S \<noteq> []"
    using Some_those_length[OF S_def[symmetric]] i1
    by auto
  moreover have "B = interval_list_union S"
    using assms(2) S_def
    by (simp add: Ds_def[symmetric])
  ultimately have Si_subset_B: "\<And>i. i < length S \<Longrightarrow> set_of (S ! i) \<subseteq> set_of B"
     using interval_list_union_correct
     by auto
  
  have "i < length S"
    using Some_those_length[OF S_def[symmetric]] i1
    by simp
  from Some_those_nth[OF S_def[symmetric] this]
  have SomeSi: "Some (S ! i) = compute_bound_fa prec f (Ds ! i)"
    by (simp add: i1)
  
  from Si_subset_B[OF \<open>i < length S\<close>]
  have "set_of (S ! i) \<subseteq> set_of (B::real interval)"
    by (simp add: interval_map_def set_of_def)
  thus ?thesis
    using compute_bound_fa_correct[OF i2 SomeSi]
    by auto
qed

ML \<open>Reification.conv @{context} @{thms interpret_form_equations} @{cterm "pi * sin y + exp' x::real"}\<close>

end