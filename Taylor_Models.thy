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

(* Trying out arithmetic on intervals and polynomials with interval coefficients. *)
value "Ivl (-1::float) 1 + Ivl 0 1"
value "Ivl (-8::float) 2 + Ivl (-2) (-1)"
value "Ivl (0::real) 1 * Ivl 0 1"
value "Ivl (-10::real) 6 * Ivl (-4) 2"
value "Ivl (-1::real) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 * Ivl 0 1"
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 (-6))] (poly.Add (poly.C (Ivl (Float 3 (-5)) (Float 3 (-5)))) (poly.Bound 0))"


subsection \<open>Computing interval bounds on arithmetic expressions\<close>

(* TODO: For now, I hard-code the precision, because I don't want to pass it around. *)
definition prec::nat where "prec=64"
fun compute_bound :: "floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_bound p I = (case approx prec p (map (Some o proc_of) I) of Some (a, b) \<Rightarrow> (if a \<le> b then Some (Ivl a b) else None) | _ \<Rightarrow> None)"

value "compute_bound (Add (Var 0) (Num 3)) [Ivl 1 2]"

lemma nonempty_compute_bound:
assumes "Some i = compute_bound f I"
shows "nonempty i"
proof-
  obtain l u where lu_def: "approx prec f (map (Some \<circ> proc_of) I) = Some (l, u)"
    using assms
    by (simp, metis (no_types, lifting) option.case_eq_if option.collapse option.distinct(1) prod.collapse)
  thus ?thesis
    using assms
    apply(simp add: lu_def)
    by (metis less_eq_float.rep_eq nonempty.simps option.distinct(1) option.sel)
qed

lemma compute_bound_correct:
fixes i::"real list"
assumes "i all_in I"
assumes "Some ivl = compute_bound f I"
shows "interpret_floatarith f i \<in> set_of ivl"
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
      from `i all_in I` this
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
          assume assm: "approx prec f (map Some (zip a b)) = None"
          from assms(2)[unfolded compute_bound.simps I_def, simplified]
          show "False"
            by (simp add: assm case_prod_beta comp_def)
        next
          fix ab' assume assm: "approx prec f (map Some (zip a b)) = Some ab'"
          obtain a' b' where ab'_def: "ab' = (a', b')"
            using old.prod.exhaust by blast
          from assms(2)[unfolded compute_bound.simps I_def]
          show False using contr_assm assm 
            by (cases "real a' \<le> real b'", simp_all add: ab'_def ivl_def case_prod_beta comp_def)
        qed
    qed
  ultimately show ?thesis
    using approx by (auto simp: ivl_def)
qed


subsection \<open>Definition of taylor models and notion of validity\<close>

(* Taylor models are a pair of a polynomial and an absolute error bound. *)
datatype taylor_model = TaylorModel "float poly" "float interval"

(* A taylor model of function f on interval I is valid, iff
     - its error bound is non-empty
     - its polynomial has the right number of parameters
     - and it is close to f on I.
*)
primrec valid_tm :: "float interval list \<Rightarrow> (real list \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> bool"
where "valid_tm I f (TaylorModel p e) = (nonempty e \<and> num_params p \<le> length I \<and> (\<forall>x. x all_in I \<longrightarrow> f x - Ipoly x (p::real poly) \<in> set_of e))"

lemma valid_tmD[elim]:
assumes "valid_tm I f t"
obtains p l u
where "t = TaylorModel p (Ivl l u)"
and   "nonempty (Ivl l u)"
and   "num_params p \<le> length I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}"
proof-
  from assms obtain p e where t_def: "t = TaylorModel p e"
    using taylor_model.exhaust by auto
  obtain l u where e_def: "e = Ivl l u"
    using interval.exhaust by auto
      
  show ?thesis
    apply(rule, simp add: t_def(1) e_def)
    using assms by (auto simp: t_def e_def)
qed

lemma valid_tmD':
assumes "valid_tm I f t"
obtains p e
where "t = TaylorModel p e"
and   "nonempty e"
and   "num_params p \<le> length I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> set_of e"
using assms by auto

lemma valid_tmI[intro]:
assumes "t = TaylorModel p (Ivl l u)"
and   "nonempty (Ivl l u)"
and   "num_params p \<le> length I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> {l..u}"
shows "valid_tm I f t"
using assms by (auto simp: valid_tm_def)

lemma valid_tmI':
assumes "t = TaylorModel p e"
and   "nonempty e"
and   "num_params p \<le> length I"
and   "\<And>x. x all_in I \<Longrightarrow> f x - Ipoly x (p::real poly) \<in> set_of e"
shows "valid_tm I f t"
using assms by (auto simp: valid_tm_def)


subsection \<open>Interval bounds for taylor models\<close>

(* Bound a polynomial by simply evaluating it with interval arguments.
   TODO: This naive approach introduces significant over-approximation. *)
fun compute_bound_poly :: "float poly \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float interval"
where "compute_bound_poly p I a = Ipoly I p"

fun compute_bound_tm :: "taylor_model \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float interval"
where "compute_bound_tm (TaylorModel p e) I a = compute_bound_poly p I a + e"

lemma compute_bound_poly_correct:
assumes "num_params p \<le> length I"
assumes "x all_in I"
assumes "a all_in I"
shows "Ipoly x (poly_map real p) \<in> set_of (compute_bound_poly p I a)"
proof-
  have "Ipoly x (poly_map real p) \<in> set_of (Ipoly (map (interval_map real) I) (poly_map interval_of (poly_map real p)))"
    apply(rule Ipoly_interval_args_mono[OF assms(2)])
    using assms(1) by simp
  also have "... = set_of (interval_map real (Ipoly I (poly_map interval_of p)))"
    apply(rule arg_cong[where f=set_of])
    using assms(1)
    by (induction p, simp_all)
  finally show ?thesis
    by simp
qed

lemma compute_bound_tm_correct:
fixes I :: "float interval list"
fixes x :: "real list"
fixes f :: "real list \<Rightarrow> real"
assumes "valid_tm I f t"
assumes "x all_in I"
assumes "a all_in I"
shows "f x \<in> set_of (compute_bound_tm t I a)"
proof-
  obtain p l u where t_def: "t = TaylorModel p (Ivl l u)"
    by (metis interval.exhaust taylor_model.exhaust)
    
  from assms have valid:
    "num_params p \<le> length I"
    "f x - Ipoly x p \<in> set_of (Ivl l u)"
      by (auto simp: t_def)
     
  show "f x \<in> set_of (compute_bound_tm t I a)"
    using set_of_add_mono[OF compute_bound_poly_correct[OF valid(1) assms(2) assms(3)] valid(2)]
    by (simp add: t_def del: compute_bound_poly.simps)
qed


subsection \<open>Computing taylor models for basic, univariate functions\<close>

fun tm_const :: "float \<Rightarrow> taylor_model"
where "tm_const c = TaylorModel (poly.C c) (Ivl 0 0)"

fun tm_id :: "nat \<Rightarrow> taylor_model"
where "tm_id n = TaylorModel (poly.Bound n) (Ivl 0 0)"

lemma tm_const_valid:
shows "valid_tm I (interpret_floatarith (Num c)) (tm_const c)"
by simp

lemma tm_id_valid:
assumes "n < length I"
shows "valid_tm I (interpret_floatarith (Var n)) (tm_id n)"
using assms by simp


subsubsection \<open>Automatic derivation of floatarith expressions\<close>

definition Sin::"floatarith \<Rightarrow> floatarith"
where "Sin a = Cos (Add a (Mult Pi (Num (Float (-1) (- 1)))))"

(* Compute the nth derivative of a floatarith expression *)
fun deriv :: "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
where "deriv v f 0 = f"
    | "deriv v f (Suc n) = DERIV_floatarith v (deriv v f n)"
    
value "map_option (interval_map real) (compute_bound (Cos (Var 0)) [Ivl (-1) 1])"

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

(* Faster derivation for univariate functions, producing smaller terms. *)
(* TODO: Extend to Inverse and Arctan! *)
fun deriv_0 :: "floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
where "deriv_0 (Cos (Var 0)) n = (case n mod 4
         of 0 \<Rightarrow> Cos (Var 0)
         | Suc 0 \<Rightarrow> Minus (Sin (Var 0))
         | Suc (Suc 0) \<Rightarrow> Minus (Cos (Var 0))
         | Suc (Suc (Suc 0)) \<Rightarrow> Sin (Var 0))"
    | "deriv_0 f n = deriv 0 f n"

lemma deriv_0_correct:
assumes "isDERIV 0 f [t]"
shows "((\<lambda>x. interpret_floatarith (deriv_0 f n) [x]) has_real_derivative interpret_floatarith (deriv_0 f (Suc n)) [t]) (at t)"
apply(cases "(f, n)" rule: deriv_0.cases)
apply(safe)
defer
using deriv_correct[OF assms]
apply(simp_all)[31]
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
qed

lemma deriv_0_0[simp]:
shows "deriv_0 f 0 = f"
by (cases "(f, 0::nat)" rule: deriv_0.cases, simp_all)


subsubsection \<open>Automatic computation of taylor coefficients for univariate functions\<close>

(* The interval coefficients of the taylor polynomial,
   i.e. the real coefficients approximated by a float interval. *)
fun tmf_c :: "nat \<Rightarrow> float interval \<Rightarrow> floatarith \<Rightarrow> float interval option"
where "tmf_c n i f = compute_bound (Mult (deriv_0 f n) (Inverse (Num (fact n)))) [i]"

(* Make a list of the n coefficients. *) 
fun tmf_cs' :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> float interval option list"
where "tmf_cs' 0 I a f = []"
    | "tmf_cs' (Suc n) I a f = (tmf_c n (interval_of a) f) # (tmf_cs' n I a f)"

(* Also add the n+1-th coefficient, representing the error contribution, and reorder the list. *)
fun tmf_cs :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> float interval list option"
where "tmf_cs n I a f = those (rev (tmf_c n I f # (tmf_cs' n I a f)))"

value "map (interval_map real) (the (tmf_cs 10 (Ivl 0 2) 1 (Cos (Var 0))))"

lemma tmf_c_correct:
fixes A::"float interval" and I::"float interval" and f::floatarith and a::real
assumes "a \<in> set_of A"
assumes "Some I = tmf_c i A f"
shows "nonempty I"
and   "interpret_floatarith (deriv_0 f i) [a] / fact i \<in> set_of I"
proof-
  obtain l u where I_decomp: "I = Ivl l u" using interval.exhaust by auto

  show result: "interpret_floatarith (deriv_0 f i) [a] / fact i \<in> set_of (interval_map real I)"
    using compute_bound_correct[OF _  assms(2)[unfolded tmf_c.simps], where i="[a]"] assms(1)
    by (simp add: divide_real_def fact_real_float_equiv)
  hence "set_of (interval_map real I) \<noteq> {}"
    by auto
  thus "nonempty I"
    by (simp add: I_decomp)
qed

lemma tmf_cs_length:
assumes "Some cs = tmf_cs n A a f"
shows "length cs = n + 1"
apply(simp add: Some_those_length[OF assms[unfolded tmf_cs.simps]])
by (induction n, simp_all)

lemma tmf_cs_correct:
fixes A::"float interval" and f::floatarith
assumes "a \<in> set_of A"
assumes "Some cs = tmf_cs n A a f"
shows "\<And>i. i < n \<Longrightarrow> Some (cs!i) = tmf_c i (interval_of a) f"
and   "Some (cs!n) = tmf_c n A f"
proof-
  from tmf_cs_length[OF assms(2)]
  have n_ineq: "n < length cs"
    by simp
  from tmf_cs_length[OF assms(2)] assms(2)
  have total_length: "length (tmf_c n A f # tmf_cs' n A a f) = Suc n"
    by (metis Some_those_length Suc_eq_plus1 tmf_cs.simps length_rev)
    
  from Some_those_nth[OF assms(2)[unfolded tmf_cs.simps] n_ineq]
  show "Some (cs ! n) = tmf_c n A f"
    apply(subst (asm) rev_nth)
    using total_length by auto
next
  fix i assume "i < n"
  from tmf_cs_length[OF assms(2)] this
  have i_ineq: "i < length cs"
    by simp

  from tmf_cs_length[OF assms(2)] assms(2)
  have total_length: "length (tmf_c n A f # tmf_cs' n A a f) = Suc n"
    by (metis Some_those_length Suc_eq_plus1 tmf_cs.simps length_rev)
    
  have "Some (cs ! i) = (tmf_c n A f # tmf_cs' n A a f) ! (n - i)"
    using Some_those_nth[OF assms(2)[unfolded tmf_cs.simps] i_ineq]
    apply(subst (asm) rev_nth)
    using total_length `i < n`
    by auto
  also have "... = (tmf_cs' n A a f) ! (n - Suc i)"
    using `i < n` by simp
  also have "...  = tmf_c i (interval_of a) f"
    using `i < n` by (induction n, auto simp: less_Suc_eq)
  finally show "Some (cs ! i) = tmf_c i (interval_of a) f" .
qed

lemma tmf_cs_nonempty:
fixes A::"float interval" and f::floatarith
assumes "a \<in> set_of A"
assumes "Some cs = tmf_cs n A a f"
shows "\<And>i. i \<le> n \<Longrightarrow> nonempty (cs!i)"
using tmf_c_correct(1)[OF _ tmf_cs_correct(1)[OF assms], where a=a, simplified] 
      tmf_c_correct(1)[OF _ tmf_cs_correct(2)[OF assms], where a=a, simplified, OF assms(1)]
by (auto simp: nat_less_le)


subsubsection \<open>Computing taylor models for arbitrary univariate expressions\<close> 

abbreviation "x_minus_a\<equiv>\<lambda>a. poly.Sub (poly.Bound 0) (poly.C a)"
fun tm_floatarith' :: "float \<Rightarrow> float interval list \<Rightarrow> float poly \<times> float interval poly"
where "tm_floatarith' a [] = (poly.C 0, poly.C 0)"
    | "tm_floatarith' a (c # cs) = (\<lambda>(pf, pi). (poly.Add (poly.C (mid c)) (poly.Mul (x_minus_a a) pf), poly.Add (poly.C (centered c)) (poly.Mul (x_minus_a (interval_of a)) pi))) (tm_floatarith' a cs)"

(* Compute a taylor model from an arbitrary, univariate floatarith expression, if possible.
   This is used to compute taylor models for elemental functions like sin, cos, exp, etc. *)
fun tm_floatarith :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "tm_floatarith n I a f = map_option (\<lambda>(pf, pi). TaylorModel pf (Ipoly [I] pi)) (map_option (tm_floatarith' a) (tmf_cs n I a f))"

lemma tm_floatarith_valid:
assumes "0 < n"
assumes "a \<in> set_of I"
assumes "\<And>x. x \<in> set_of I \<Longrightarrow> isDERIV 0 f [x]"
assumes "Some t = tm_floatarith n I a f"
shows "valid_tm [I] (interpret_floatarith f) t"
proof-
  from assms(4)[unfolded tm_floatarith.simps]
  obtain pf pi where Some_pf_pi_def: "Some (pf, pi) = map_option (tm_floatarith' a) (tmf_cs n I a f)"
    by (metis (no_types, lifting) map_option_eq_Some prod.collapse)
  then have t_def: "t = TaylorModel pf (Ipoly [I] pi)"
    using assms(4)[unfolded tm_floatarith.simps]
    by (metis old.prod.case option.sel option.simps(9))
  from Some_pf_pi_def obtain cs where cs_def: "Some cs = tmf_cs n I a f"
    by (metis map_option_eq_Some)
  have pfpi_def: "(pf, pi) = tm_floatarith' a cs"
    by (metis Some_pf_pi_def cs_def map_option_eq_Some option.sel)
  from tmf_cs_nonempty[OF assms(2) cs_def] tmf_cs_length[OF cs_def]
  have valid_cs: "\<And>i. i < length cs \<Longrightarrow> nonempty (cs ! i)"
    by auto
  
  show ?thesis
  proof(rule valid_tmI')
    show "t = TaylorModel pf (Ipoly [I] pi)"
      by (simp add: t_def)
  next
    show "nonempty (Ipoly [I] pi)"
      using pfpi_def valid_cs
      apply(induction cs arbitrary: pf pi)
      apply(simp add: zero_interval_def)
      proof-
        case (Cons c cs pf pi)
        then obtain pf' pi' where pf'pi'_def: "(pf', pi') = tm_floatarith' a cs"
          using prod.collapse by blast
        from this Cons(2)[simplified]
        have pi_decomp: "pi = poly.Add (c - Ivl (mid c) (mid c))\<^sub>p (Mul (x_minus_a (Ivl a a)) pi')"
          by (metis old.prod.case prod.sel(2))
        show ?case
          by (simp add: pi_decomp Cons(3)[of 0, simplified] nonempty_sub nonempty_add)
      qed
  next
    show "num_params pf \<le> length [I]"
      using pfpi_def
      apply(induction cs arbitrary: pf pi)
      apply(simp)
      proof-
        case (Cons c cs pf pi)
        then obtain pf' pi' where pf'pi'_def: "(pf', pi') = tm_floatarith' a cs"
          using prod.collapse by blast
        from this Cons(2)[simplified]
        have pf_decomp: "pf = poly.Add (mid c)\<^sub>p (Mul (x_minus_a a) pf')"
          by (metis old.prod.case prod.sel(1))
        show ?case
          using Cons(1)[OF pf'pi'_def]
          by (simp add: pf_decomp)
      qed
  next
    fix xs assume hyp: "xs all_in map (interval_map real) [I]"
    from hyp obtain x where xs_def: "xs = [x]" by (auto simp: length_Suc_conv)
    hence x_def: "x \<in> set_of I" using hyp by simp
    
    show "interpret_floatarith f xs - Ipoly xs (poly_map real pf) \<in> set_of (Ipoly [I] pi)"
    proof(cases "x = a")
      case True
      have pf_val_at_a: "Ipoly [real a] (poly_map real pf) = mid (cs ! 0)"
        using pfpi_def tmf_cs_length[OF cs_def]
        apply(induction cs arbitrary: pf pi n)
        apply(simp)
        proof-
          case (Cons c cs pf pi n)
          then obtain pf' pi' where pf'pi'_def: "(pf', pi') = tm_floatarith' a cs"
            using prod.collapse by blast
          from this Cons(2)[simplified]
          have pf_decomp: "pf = poly.Add (mid c)\<^sub>p (Mul (x_minus_a a) pf')"
            by (metis old.prod.case prod.sel(1))
          show ?case
            using Cons(1)[OF pf'pi'_def]
            by (simp add: pf_decomp)
        qed
      from tmf_c_correct(2)[OF _ tmf_cs_correct(1)[OF assms(2) cs_def assms(1)], of a]
      have "interpret_floatarith f xs \<in> set_of (interval_map real (cs ! 0))"
        by (simp add: xs_def `x = a`)
      have "interpret_floatarith f xs - Ipoly xs (poly_map real pf) \<in> set_of (interval_map real (cs ! 0) - (mid (cs ! 0)))"
        using pf_val_at_a tmf_c_correct(2)[OF _ tmf_cs_correct(1)[OF assms(2) cs_def assms(1)], of a]
        by (simp add: xs_def `x = a` set_of_minus_mono)
      also have "... \<subseteq>  set_of (interval_map real (Ipoly [I] pi))"
        proof-
          from tmf_cs_length[OF cs_def]
          obtain c cs' where cs_decomp: "cs = c # cs'" 
            by (metis Suc_eq_plus1 list.size(3) neq_Nil_conv old.nat.distinct(2))
          obtain pi' where pi_decomp: "pi = poly.Add (c - interval_of (mid c))\<^sub>p (Mul (x_minus_a (interval_of a)) pi')"
            using pfpi_def
            by (simp add: cs_decomp case_prod_beta)
            
          show ?thesis
            apply(simp add: cs_decomp pi_decomp)
            apply(rule set_of_add_inc[where B=0, simplified])
            using valid_cs[of 0] tmf_cs_length[OF cs_def]
            apply(simp add: nonempty_sub cs_decomp)
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
                  (\<Sum>m<n. interpret_floatarith (deriv_0 f m) [real a] / fact m * (x - real a) ^ m)
                  + interpret_floatarith (deriv_0 f n) [t] / fact n * (x - real a) ^ n"
        apply(rule taylor[where a=l and b=u])
        apply(rule `0 < n`)
        apply(simp)
        apply(safe)[1]
        apply(rule deriv_0_correct[OF assms(3)])
        apply(simp add: I_def)
        using assms(2) x_def `x \<noteq> a`
        by (simp_all add: I_def)
      then obtain t 
      where "if x < real a then x < t \<and> t < real a else real a < t \<and> t < x"
      and taylor_expansion:
        "interpret_floatarith f [x] = 
           (\<Sum>m<n. interpret_floatarith (deriv_0 f m) [real a] / fact m * (x - real a) ^ m)
           + interpret_floatarith (deriv_0 f n) [t] / fact n * (x - real a) ^ n"
        by auto
      from this(1) have t_in_I: "t \<in> set_of I"
        using assms(2) x_def
        apply(simp add: I_def)
        by (meson less_eq_real_def order_trans)
      
      from pfpi_def tmf_cs_length[OF cs_def]
      have Ipoly_pf_eq: "Ipoly xs pf = (\<Sum>m<Suc n. mid (cs!m) * (x - a) ^ m)"
        apply(induction cs arbitrary: n pf pi)
        apply(simp add: xs_def)
        proof-
          case (Cons c cs n pf pi)
          obtain pf' pi' where pf'pi'_def: "(pf', pi') = tm_floatarith' a cs"
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
      
      def cr\<equiv>"\<lambda>i. if i < n then (interpret_floatarith (deriv_0 f i) [real a] / fact i - real (mid (cs ! i)))
                           else (interpret_floatarith (deriv_0 f i) [t] / fact n - real (mid (cs ! i)))"
      def ci\<equiv>"\<lambda>i. (interval_map real (cs ! i) - interval_of (real (mid (cs ! i))))"
      
      have "(\<Sum>m<n. interpret_floatarith (deriv_0 f m) [real a] / fact m * (x - real a) ^ m)
                 + interpret_floatarith (deriv_0 f n) [t] / fact n * (x - real a) ^ n
                 - Ipoly xs (poly_map real pf)
                 = (\<Sum>m<n. cr m  * (x - real a) ^ m) + cr n * (x - real a) ^ n"
        by (simp add: Ipoly_pf_eq algebra_simps setsum.distrib[symmetric] cr_def)
      also have "... = horner_eval cr (x - real a) (Suc n)"
        by (simp add: horner_eval_eq_setsum)
      also have "... \<in> set_of (horner_eval ci (x - real a) (Suc n))"
        apply(rule horner_eval_interval)
        apply(simp add: cr_def ci_def)
        apply(safe)[1]
        using tmf_c_correct(2)[OF _ tmf_cs_correct(1)[OF  assms(2) cs_def], where a=a, simplified]
        apply(simp)
        apply(rule set_of_minus_mono)
        using tmf_c_correct(2)[OF t_in_I tmf_cs_correct(2)[OF assms(2) cs_def]]
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
        using ci_def pfpi_def tmf_cs_length[OF cs_def] valid_cs
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
          from cs_def obtain pf' pi' where pf'pi'_def: "(pf', pi') = tm_floatarith' a cs'"
            using prod.collapse by blast
          from Suc(2) have pi_def: "pi = poly.Add (centered c)\<^sub>p (Mul (x_minus_a (Ivl a a)) pi')"
            by (simp add: cs_def pf'pi'_def[symmetric])
            
          have "set_of (horner_eval (\<lambda>i. interval_map real (cs ! i) - interval_of (real (mid (cs ! i)))) (interval_of (x - real a)) (Suc (Suc n)))
              = set_of (interval_map real (c) - interval_of (real (mid c))
                        + interval_of (x - real a) * horner_eval (\<lambda>i. interval_map real (cs' !  i) - interval_of (real (mid (cs' ! i)))) (interval_of (x - real a)) (Suc n))"
            by (simp add: cs_def)
          also have "... \<subseteq> set_of (interval_map real (c) - interval_of (real (mid c)) + interval_of (x - real a) * interval_map real (Ipoly [I] pi'))"
            apply(rule set_of_add_inc_right)
            apply(rule nonempty_mul)
            apply(rule set_of_mul_inc_right)
            prefer 2
            apply(rule Suc(1)[OF pf'pi'_def length_cs'])
            using Suc(4)[unfolded cs_def] length_cs'
            apply (metis Suc.prems(2) Suc_eq_plus1 Suc_less_eq2 cs_def nth_Cons_Suc)
            using Suc(4)[unfolded cs_def, of 1, simplified, OF `cs' \<noteq> []`]
            by (simp add: nonempty_add nonempty_sub)
          also have "... \<subseteq> set_of (interval_map real (Ipoly [I] pi))"
            apply(simp add: pi_def)
            apply(rule set_of_add_inc_right)
            apply(rule nonempty_mul)
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


subsection \<open>Operations on taylor models\<close>

fun tm_neg :: "taylor_model \<Rightarrow> taylor_model"
where "tm_neg (TaylorModel p i) = TaylorModel (poly.Neg p) (-i)"

fun tm_add :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_add (TaylorModel p1 i1) (TaylorModel p2 i2) = TaylorModel (poly.Add p1 p2) (i1+i2)"

fun tm_sub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "tm_sub t1 t2 = tm_add t1 (tm_neg t2)"

(* TODO: Currently, this increases the degree of the polynomial! *)
fun tm_mul :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model"
where "tm_mul (TaylorModel p1 i1) (TaylorModel p2 i2) I a = (
  let d1=compute_bound_poly p1 I a;
      d2=compute_bound_poly p2 I a
  in TaylorModel (poly.Mul p1 p2) (i1*d2 + d1*i2 + i1*i2))"
  
fun tm_pow :: "taylor_model \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model"
where "tm_pow t 0 I a = TaylorModel (poly.C 1) (Ivl 0 0)"
    | "tm_pow t (Suc n) I a = tm_mul t (tm_pow t n I a) I a"

fun tm_inc_error :: "taylor_model \<Rightarrow> float interval \<Rightarrow> taylor_model"
where "tm_inc_error (TaylorModel p e) i = TaylorModel p (e+i)"

(* Evaluates a float polynomial, using a taylor model as the parameter. This is used to compose taylor models. *)
fun eval_poly_at_tm :: "float poly \<Rightarrow> taylor_model \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model"
where "eval_poly_at_tm (poly.C c) t I a = tm_const c"
    | "eval_poly_at_tm (poly.Bound n) t I a = (if n = 0 then t else undefined)"
    | "eval_poly_at_tm (poly.Add p1 p2) t I a = tm_add (eval_poly_at_tm p1 t I a) (eval_poly_at_tm p2 t I a)"
    | "eval_poly_at_tm (poly.Sub p1 p2) t I a = tm_sub (eval_poly_at_tm p1 t I a) (eval_poly_at_tm p2 t I a)"
    | "eval_poly_at_tm (poly.Mul p1 p2) t I a = tm_mul (eval_poly_at_tm p1 t I a) (eval_poly_at_tm p2 t I a) I a"
    | "eval_poly_at_tm (poly.Neg p) t I a = tm_neg (eval_poly_at_tm p t I a)"
    | "eval_poly_at_tm (poly.Pw p n) t I a = tm_pow (eval_poly_at_tm p t I a) n I a"
    | "eval_poly_at_tm (poly.CN c n p) t I a = tm_add (eval_poly_at_tm c t I a) (tm_mul (if n = 0 then t else undefined) (eval_poly_at_tm p t I a) I a)"

fun tm_comp :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> taylor_model"
where "tm_comp (TaylorModel p e) t I a = tm_inc_error (eval_poly_at_tm p t I a) e"

(* Validity of is preserved under taylor model arithmetic. *)
lemma tm_neg_valid:
assumes "valid_tm I f t"
shows "valid_tm I (-f) (tm_neg t)"
proof-
  from valid_tmD[OF assms]
  obtain p l u where t_def: 
    "t = TaylorModel p (Ivl l u)"
    "nonempty (Ivl l u)"
    "num_params p \<le> length I"
    "\<And>x::real list. x all_in I \<Longrightarrow> f x - Ipoly x p \<in> {l..u}"
      by blast
  show ?thesis
    apply(rule)
    apply(simp add: t_def(1) uminus_interval_def)
    using t_def(2)
    apply(simp)
    apply(simp add: t_def(3))
    proof-
      fix x::"real list" assume assms: "x all_in I"
      show "(-f) x - Ipoly x (Neg p) \<in> {(-u)..(-l)}"
        using t_def(4)[OF assms] by simp
    qed
qed

lemma tm_add_valid:
assumes "valid_tm I f t1"
assumes "valid_tm I g t2"
shows "valid_tm I (f + g) (tm_add t1 t2)"
proof-
  from valid_tmD[OF assms(1)]
  obtain p1 l1 u1 where t1_def:
    "t1 = TaylorModel p1 (Ivl l1 u1)"
    "nonempty (Ivl l1 u1)"
    "num_params p1 \<le> length I"
    "\<And>x::real list. x all_in I \<Longrightarrow> f x - Ipoly x p1 \<in> {l1..u1}"
      by blast
  from valid_tmD[OF assms(2)]
  obtain p2 l2 u2 where t2_def:
    "t2 = TaylorModel p2 (Ivl l2 u2)"
    "nonempty (Ivl l2 u2)"
    "num_params p2 \<le> length I"
    "\<And>x::real list. x all_in I \<Longrightarrow> g x - Ipoly x p2 \<in> {l2..u2}"
      by blast
   
  show "valid_tm I (f + g) (tm_add t1 t2)"
    proof(rule)
      show "num_params (poly.Add p1 p2) \<le> length I"
      by (simp add: t1_def(3) t2_def(3))
    next
      fix x::"real list" assume assms: "x all_in I"
      from t1_def(4)[OF this] t2_def(4)[OF this]
       show "(f + g) x - Ipoly x (poly.Add p1 p2) \<in> {(l1+l2)..(u1+u2)}"
        by simp
    next
      show "nonempty (Ivl (l1 + l2) (u1 + u2))"
        using t1_def(2) t2_def(2)
        by simp
    qed (simp add: t1_def(1) t2_def(1) plus_interval_def)
qed

lemma tm_sub_valid:
assumes "valid_tm I f t1"
assumes "valid_tm I g t2"
shows "valid_tm I (f - g) (tm_sub t1 t2)"
using tm_add_valid[OF assms(1) tm_neg_valid[OF assms(2)]]
by simp

(* TODO: Clean this proof up! *)
lemma tm_mul_valid:
assumes "valid_tm I f t1"
assumes "valid_tm I g t2"
assumes "all_nonempty I"
assumes "a all_in I"
shows "valid_tm I (f * g) (tm_mul t1 t2 I a)"
proof-
  from valid_tmD'[OF assms(1)]
  obtain p1 i1 where t1_def:
    "t1 = TaylorModel p1 i1"
    "nonempty i1"
    "num_params p1 \<le> length I"
    "\<And>x::real list. x all_in I \<Longrightarrow> f x - Ipoly x p1 \<in> set_of i1"
      by blast
  from valid_tmD'[OF assms(2)]
  obtain p2 i2 where t2_def:
    "t2 = TaylorModel p2 i2"
    "nonempty i2"
    "num_params p2 \<le> length I"
    "\<And>x::real list. x all_in I \<Longrightarrow> g x - Ipoly x p2 \<in> set_of i2"
      by blast
  
  have v1: "nonempty (Ipoly I (poly_map interval_of p1))"
    by (rule nonempty_Ipoly[OF assms(3) t1_def(3)])
  have v2: "nonempty (Ipoly I (poly_map interval_of p2))"
    by (rule nonempty_Ipoly[OF assms(3) t2_def(3)])
      
  show "valid_tm I (f * g) (tm_mul t1 t2 I a)"
    unfolding t1_def t2_def tm_mul.simps Let_def
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
      
      have "(f * g) x = f x * g x"
        by auto
      also have "... = (d1 + Ipoly x p1) * (d2 + Ipoly x p2)"
        by (simp add: d1_def(2)[symmetric] d2_def(2)[symmetric])
      also have "... = Ipoly x p1 * Ipoly x p2 + d1 * Ipoly x p2 + Ipoly x p1 * d2 + d1 * d2"
        by (simp add: algebra_simps)
      finally have f_times_g_eq: "(f * g) x - Ipoly x p1 * Ipoly x p2 = d1 * Ipoly x p2 + Ipoly x p1 * d2 + d1 * d2"
        by simp
      also have "... \<in> set_of (i1 * compute_bound_poly p2 I a) +  set_of (compute_bound_poly p1 I a * i2) + set_of (i1 * i2)"
        apply(rule set_plus_intro[OF set_plus_intro])
        using d1_def(1) d2_def(1) compute_bound_poly_correct[OF t1_def(3) 1(1) `a all_in I`] compute_bound_poly_correct[OF t2_def(3) 1(1) `a all_in I`]
        by (simp_all add: set_of_mult_mono)
      also have "... = set_of (i1 * compute_bound_poly p2 I a + compute_bound_poly p1 I a * i2 + i1 * i2)"
        by (simp add: v1 v2 t1_def(2) t2_def(2) set_of_add_distrib nonempty_add)
      finally have "(f * g) x - Ipoly x p1 * Ipoly x p2  \<in> set_of (i1 * compute_bound_poly p2 I a + compute_bound_poly p1 I a * i2 + i1 * i2)"
        .
      thus ?case by simp
    next
      case 2
      show ?case
        using t1_def(2) t2_def(2) v1 v2
        by (simp add: nonempty_add)
    qed
qed

lemma tm_pow_valid:
assumes "valid_tm I f t"
assumes "all_nonempty I"
assumes "a all_in I"
shows "valid_tm I (f ^ n) (tm_pow t n I a)"
apply(induction n, simp)
using assms(1) tm_mul_valid[OF _ _ assms(2,3)]
by force
        
lemma tm_comp_valid:
assumes "all_nonempty I"
(* TODO: Can I rewrite this and make this simpler? *)
assumes gI_def: "\<And>x. length x = length I \<Longrightarrow> (\<forall>n<length I. x!n \<in> set_of (I!n)) \<Longrightarrow> g x \<in> set_of gI"
assumes t1_def: "valid_tm [gI] (\<lambda>x. f (x ! 0)) t1"
assumes t2_def: "valid_tm I g t2"
assumes "a all_in I"
shows "valid_tm I (f o g) (tm_comp t1 t2 I a)"
proof-
  obtain pf ef where t1_decomp: "t1 = TaylorModel pf ef" using taylor_model.exhaust by auto
  obtain pg eg where t2_decomp: "t2 = TaylorModel pg eg" using taylor_model.exhaust by auto
  
  from t1_def have t1_valid:
    "nonempty ef"
    "num_params pf \<le> 1"
    "\<And>x::real list. x all_in I \<Longrightarrow> f (g x) - Ipoly [g x] (poly_map real pf) \<in> set_of ef"
      using gI_def
      by (simp_all add: t1_decomp, metis length_Cons list.size(3) nth_Cons_0)
      
  from t2_def have t2_valid:
    "nonempty eg"
    "num_params pg \<le> length I"
    "\<And>x::real list. x all_in I \<Longrightarrow> g x - Ipoly x (poly_map real pg) \<in> set_of (interval_map real eg)"
      by (auto simp: t2_decomp)
      
  obtain p' e' where p'e'_def: "TaylorModel p' e' = eval_poly_at_tm pf t2 I a"
    using taylor_model.exhaust by metis
    
  have "valid_tm I ((\<lambda>x. Ipoly [x] pf) o g) (eval_poly_at_tm pf t2 I a)"
    using t1_valid(2)
    proof(induction pf)
      case (C c) thus ?case
        by simp
    next
      case (Bound n) thus ?case
        by (simp add: t2_decomp t2_valid)
    next
      case (Add p1l p1r) thus ?case 
        using tm_add_valid by (simp add: func_plus)
    next
      case (Sub p1l p1r) thus ?case 
        using tm_sub_valid by (simp add: fun_diff_def)
    next
      case (Mul p1l p1r) thus ?case 
        using tm_mul_valid[OF _ _ `all_nonempty I` `a all_in I`] by (simp add: func_times)
    next
      case (Neg p1') thus ?case 
        using tm_neg_valid by (simp add: fun_Compl_def)
    next
      case (Pw p1' n) thus ?case 
        using tm_pow_valid[OF _ `all_nonempty I` `a all_in I`] by (simp add: fun_pow)
    next
      case (CN p1l n p1r) thus ?case 
        using tm_add_valid[OF _ tm_mul_valid[OF _ _ `all_nonempty I` `a all_in I`], unfolded func_plus func_times] t2_def by simp
    qed
     
  hence eval_poly_at_tm_valid:
    "nonempty e'"
    "num_params p' \<le> length I"
    "\<forall>x. length x = length I \<and> (\<forall>n<length I. x ! n \<in> set_of (interval_map real (I ! n))) \<longrightarrow>
         Ipoly [g x] (poly_map real pf) - Ipoly x (poly_map real p') \<in> set_of (interval_map real e')"
      by (auto simp: t1_decomp p'e'_def[symmetric])
  show ?thesis
    apply(simp add: t1_decomp p'e'_def[symmetric] del: all_in_def)
    apply(safe)
    apply(rule nonempty_add[OF eval_poly_at_tm_valid(1) t1_valid(1)])
    using eval_poly_at_tm_valid(2)
    apply(simp)
    proof(goals)
      case (1 x)
      have "Ipoly [g x] (poly_map real pf) - Ipoly x (poly_map real p') \<in> set_of e'"
        using 1 eval_poly_at_tm_valid(3)
        by simp
      thus ?case
        using set_of_add_mono t1_valid(3)[OF 1]
        by force
    qed
qed


subsection \<open>Computing taylor models for multivariate expressions\<close>

(* Compute taylor models of degree n from floatarith expressions. *)
fun compute_tm :: "nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "compute_tm _ I _ (Num c) = Some (tm_const c)"
    | "compute_tm _ I _ (Var n) = Some (tm_id n)"
    | "compute_tm n I a (Add l r) = (
         case (compute_tm n I a l, compute_tm n I a r) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_add t1 t2)
          | _ \<Rightarrow> None)"
    | "compute_tm n I a (Minus f) = map_option (\<lambda>t. tm_neg t) (compute_tm n I a f)"
    | "compute_tm n I a (Mult l r) = (
         case (compute_tm n I a l, compute_tm n I a r) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_mul t1 t2 I a)
          | _ \<Rightarrow> None)"     
    | "compute_tm n I a (Power f k) = map_option (\<lambda>t. tm_pow t k I a) (compute_tm n I a f)"
    | "compute_tm n I a (Inverse f) = (
         case compute_tm n I a f
         of Some t2 \<Rightarrow> (
           let I' = compute_bound_tm t2 I a; a' = compute_bound_tm t2 a a
           in if real (lower I') \<le> 0 \<and> 0 \<le> real (upper I') then None else
              case tm_floatarith n I' (mid a') (Inverse (Var 0))
              of Some t1 \<Rightarrow> Some (tm_comp t1 t2 I a)
              | _ \<Rightarrow> None)
         | _ \<Rightarrow> None)"
    | "compute_tm n I a (Cos f) = (
         case compute_tm n I a f
         of Some t2 \<Rightarrow> (
           case tm_floatarith n (compute_bound_tm t2 I a) (mid (compute_bound_tm t2 a a)) (Cos (Var 0))
           of Some t1 \<Rightarrow> Some (tm_comp t1 t2 I a)
           | _ \<Rightarrow> None)
         | _ \<Rightarrow> None)"
    | "compute_tm _ _ _ _ = None"

lemma compute_tm_valid:
assumes "0 < n"
assumes num_vars_f: "num_vars f \<le> length I"
assumes "all_nonempty I"
assumes "a all_in I"
assumes t_def: "Some t = compute_tm n I a f"
shows "valid_tm I (interpret_floatarith f) t"
using num_vars_f t_def
proof(induct f arbitrary: t)
  case (Add l r t)
  obtain t1 where t1_def: "Some t1 = compute_tm n I a l"
    by (metis (no_types, lifting) Add(4) compute_tm.simps(3) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "Some t2 = compute_tm n I a r"
    by (smt Add(4) compute_tm.simps(3) option.case_eq_if option.collapse prod.case)
  have t_def: "t = tm_add t1 t2"
    using Add(4) t1_def t2_def
    by (metis compute_tm.simps(3) option.case(2) option.inject prod.case)
  
  have [simp]: "interpret_floatarith (floatarith.Add l r) = interpret_floatarith l + interpret_floatarith r"
    by auto
  show "valid_tm I (interpret_floatarith (floatarith.Add l r)) t"
    apply(simp add: t_def)
    apply(rule tm_add_valid[OF Add(1)[OF _ t1_def] Add(2)[OF _ t2_def]])
    using Add(3) by auto
next
  case (Minus f t)
  have [simp]: "interpret_floatarith (Minus f) = -interpret_floatarith f"
    by auto
   
  obtain t1 where t1_def: "Some t1 = compute_tm n I a f"
    by (metis Minus.prems(2) compute_tm.simps(4) map_option_eq_Some)
  have t_def: "t = tm_neg t1"
    by (metis Minus.prems(2) compute_tm.simps(4) option.inject option.simps(9) t1_def)
  
  show "valid_tm I (interpret_floatarith (Minus f)) t"
    apply(simp add: t_def, rule tm_neg_valid[OF Minus(1)[OF _ t1_def]])
    using Minus(2) by auto
next
  case (Mult l r t)
  obtain t1 where t1_def: "Some t1 = compute_tm n I a l"
    by (metis (no_types, lifting) Mult(4) compute_tm.simps(5) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "Some t2 = compute_tm n I a r"
    by (smt Mult(4) compute_tm.simps(5) option.case_eq_if option.collapse prod.case)
  have t_def: "t = tm_mul t1 t2 I a"
    using Mult(4) t1_def t2_def
    by (metis compute_tm.simps(5) option.case(2) option.inject prod.case)
  
  have [simp]: "interpret_floatarith (floatarith.Mult l r) = interpret_floatarith l * interpret_floatarith r"
    by auto
  show "valid_tm I (interpret_floatarith (floatarith.Mult l r)) t"
    apply(simp add: t_def)
    apply(rule tm_mul_valid[OF Mult(1)[OF _ t1_def] Mult(2)[OF _ t2_def] `all_nonempty I` `a all_in I`])
    using Mult(3) by auto
next
  case (Power f k t)
  from Power(3)
  obtain tm_f where tm_f_def: "Some tm_f =  compute_tm n I a f"
    apply(simp) using map_option_eq_Some by metis
  have t_decomp: "t = tm_pow tm_f k I a"
    using Power(3) by (simp add: tm_f_def[symmetric])
  show ?case
    using tm_pow_valid[OF Power(1)[OF Power(2)[simplified] tm_f_def] `all_nonempty I` `a all_in I`]
    by (simp add: t_decomp fun_pow)
next
  case (Inverse f t)
  obtain tm_f where tm_f_def: "Some tm_f = compute_tm n I a f"
    using Inverse(3)[unfolded compute_tm.simps]
    by (metis (no_types, lifting) option.case_eq_if option.collapse)
  def I'\<equiv>"compute_bound_tm tm_f I a"
  def a'\<equiv>"compute_bound_tm tm_f a a"
  have zero_notin_I': "\<not>(real (lower I') \<le> 0 \<and> 0 \<le> real (upper I'))"
    using Inverse(3)
    by (auto simp: I'_def tm_f_def[symmetric])
  obtain tm_inv where tm_inv_def: "Some tm_inv = tm_floatarith n (I') (mid a') (Inverse (Var 0))"
    using Inverse(3)
    apply(simp add: I'_def a'_def tm_f_def[symmetric] Let_def del: tm_floatarith.simps)
    using zero_notin_I'[unfolded I'_def]
    by (metis (mono_tags, lifting) interval_of_def map_eq_conv option.case_eq_if option.collapse)
    
  have t_decomp: "t = tm_comp tm_inv tm_f I a"
    using Inverse(3)
    apply(simp add: I'_def[symmetric] a'_def[symmetric] tm_f_def[symmetric] del: tm_floatarith.simps)
    by (metis option.distinct(1) option.inject option.simps(5) tm_inv_def)
  have valid_tm_tm_f: "valid_tm I (interpret_floatarith f) tm_f"
    using Inverse(1)[OF Inverse(2)[simplified] tm_f_def] .
    
  obtain tm_f_p tm_f_e where tm_f_decomp: "tm_f = TaylorModel tm_f_p tm_f_e"
    using taylor_model.exhaust by metis
  
  have "mid (compute_bound_tm tm_f (map interval_of a) a) \<in> set_of (compute_bound_tm tm_f (map interval_of a) a)"
    apply(rule mid_in_interval)
    using valid_tm_tm_f `a all_in I`
    apply(simp add: tm_f_decomp)
    apply(rule nonempty_add[OF nonempty_Ipoly])
    by (simp_all add: nonempty_add[OF nonempty_Ipoly])
  also have "... \<subseteq> set_of (compute_bound_tm tm_f I a)"
    using `a all_in I` valid_tm_tm_f
    apply(simp add: tm_f_decomp)
    apply(rule set_of_add_inc_left[OF nonempty_Ipoly])
    apply(simp_all add: tm_f_decomp)
    apply(rule Ipoly_interval_args_inc_mono)
    by simp_all
  finally have a1: "mid (compute_bound_tm tm_f (map interval_of a) a) \<in> set_of (compute_bound_tm tm_f I a)"
    .
    
  have [simp]: "interpret_floatarith (Inverse (Var 0)) = (\<lambda>x. inverse (x ! 0))"
    by auto
    
  have I'_decomp: "I' = Ivl (lower I') (upper I')"
    by (simp add: add_left_imp_eq plus_interval_def)
  have "0 \<notin> set_of (interval_map real (compute_bound_tm tm_f I a))"
    apply(subst I'_decomp[unfolded I'_def])
    using zero_notin_I' by (simp add: I'_def)
  hence a2: "valid_tm [compute_bound_tm tm_f I a] (\<lambda>x. inverse (x ! 0)) tm_inv"
    using tm_floatarith_valid[OF `0 < n` a1 _ tm_inv_def[unfolded I'_def a'_def]] 
    by auto
    
  show ?case
    unfolding t_decomp
    using tm_comp_valid[OF `all_nonempty I` _ a2 Inverse(1)[OF _ tm_f_def] `a all_in I`]
          compute_bound_tm_correct[OF Inverse(1)[OF _ tm_f_def] _ `a all_in I`]
          tm_floatarith_valid[OF `0 < n` a1 _ tm_inv_def[unfolded I'_def a'_def]] Inverse.prems(1)
    by auto
next
  case (Cos f t)
  obtain tm_f where tm_f_def: "Some tm_f = compute_tm n I a f"
    using Cos(3)[unfolded compute_tm.simps]
    by (metis (no_types, lifting) option.case_eq_if option.collapse)
  then obtain tm_cos where tm_cos_def: "Some tm_cos = tm_floatarith n (compute_bound_tm tm_f I a) (mid (compute_bound_tm tm_f (map interval_of a) a)) (Cos (Var 0))"
    using Cos(3)[unfolded compute_tm.simps]
    by (metis (no_types, lifting) option.case_eq_if option.collapse option.simps(5))
  have t_decomp: "t = tm_comp tm_cos tm_f I a"
    using Cos(3) tm_f_def[symmetric] tm_cos_def[symmetric]
    by auto
  have valid_tm_tm_f: "valid_tm I (interpret_floatarith f) tm_f"
    using Cos(1)[OF Cos(2)[simplified] tm_f_def] .
    
  obtain tm_f_p tm_f_e where tm_f_decomp: "tm_f = TaylorModel tm_f_p tm_f_e"
    using taylor_model.exhaust by metis
  
  have "mid (compute_bound_tm tm_f (map interval_of a) a) \<in> set_of (compute_bound_tm tm_f (map interval_of a) a)"
    apply(rule mid_in_interval)
    using valid_tm_tm_f `a all_in I`
    apply(simp add: tm_f_decomp)
    apply(rule nonempty_add[OF nonempty_Ipoly])
    by (simp_all add: nonempty_add[OF nonempty_Ipoly])
  also have "... \<subseteq> set_of (compute_bound_tm tm_f I a)"
    using `a all_in I` valid_tm_tm_f
    apply(simp add: tm_f_decomp)
    apply(rule set_of_add_inc_left[OF nonempty_Ipoly])
    apply(simp_all add: tm_f_decomp)
    apply(rule Ipoly_interval_args_inc_mono)
    by simp_all
  finally have a1: "mid (compute_bound_tm tm_f (map interval_of a) a) \<in> set_of (compute_bound_tm tm_f I a)"
    .
  have a2: "valid_tm [compute_bound_tm tm_f I a] (\<lambda>x. cos (x ! 0)) tm_cos"
    using tm_floatarith_valid[OF `0 < n` a1 _ tm_cos_def, simplified]
    by auto
    
  show ?case
    unfolding t_decomp
    using tm_comp_valid[OF `all_nonempty I` _ a2 Cos(1)[OF _ tm_f_def] `a all_in I`]
          compute_bound_tm_correct[OF Cos(1)[OF _ tm_f_def] _ `a all_in I`]
          tm_floatarith_valid[OF `0 < n` a1 _ tm_cos_def] Cos.prems(1)
    by auto
qed (simp_all add: valid_tm_def)


(* Compute some taylor models. *)
value "the (compute_tm 7 [Ivl 0 2] [1] (Num 2))"
value "the (compute_tm 7 [Ivl 0 2] [1] (Var 0))"
value "the (compute_tm 7 [Ivl 0 2, Ivl 0 2] [1,1] (Add (Var 0) (Var 1)))"
value "the (compute_tm 10 [Ivl (-1) 1] [0] (Cos (Var 0)))"
(* TODO: This is far too slow! *)
value "the (compute_tm 5 [Ivl (1) 3] [2] (Inverse (Var 0)))"


subsection \<open>Computing bounds for floatarith expressions\<close>

(* Automatically find interval bounds for floatarith expressions. *)
fun compute_ivl_bound :: "nat \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> float interval option"
where "compute_ivl_bound n I f = (case compute_tm n I (map mid I) f of None \<Rightarrow> None | Some t \<Rightarrow> Some (compute_bound_tm t I (map mid I)))"

value "map_option (map_interval real) (compute_ivl_bound 10 [Ivl (-1) 1] (Power (Cos (Var 0)) 2))"

(* Automatically computed bounds are correct. *)
lemma compute_ivl_bound_correct:
assumes "0 < n"
assumes "num_vars f \<le> length I"
assumes B_def: "Some B = compute_ivl_bound n I f"
assumes "all_nonempty I"
assumes "x all_in I"
shows "interpret_floatarith f x \<in> set_of B"
proof-
  (* Since we have a bound B, there must have been a taylor model used to compute it. *)
  from assms(3) obtain t where B_def: "B = compute_bound_tm t I (map mid I)" 
                           and t_def: "Some t = compute_tm n I (map mid I) f"
    by (simp, metis (mono_tags, lifting) option.case_eq_if option.collapse option.distinct(1) option.inject)
  
  from compute_bound_tm_correct[OF compute_tm_valid[OF `0 < n` assms(2) `all_nonempty I` _ t_def] `x all_in I`]
  show ?thesis
    using `all_nonempty I`
    by (auto simp: B_def mid_in_interval)
qed

end