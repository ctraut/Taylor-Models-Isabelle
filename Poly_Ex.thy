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
fixes p1 p2 :: "float poly"
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

lemma poly_map_real_polyneg:
fixes p :: "float poly"
shows "poly_map real (~\<^sub>pp) = ~\<^sub>p(poly_map real p)"
by (induction p) simp_all

lemma poly_map_real_polysub:
fixes p1 p2 :: "float poly"
shows "poly_map real (p1 -\<^sub>p p2) = poly_map real p1 -\<^sub>p poly_map real p2"
by (simp add: polysub_def poly_map_real_polyadd poly_map_real_polyneg)
    
lemma poly_map_real_polymul:
fixes p1 p2 :: "float poly"
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

lemma poly_map_real_polypow:
fixes p :: "float poly"
shows "poly_map real (p^\<^sub>pn) = (poly_map real p)^\<^sub>pn"
proof(induction n rule: nat_less_induct)
  fix n assume assm: "\<forall>m<n. poly_map real (p ^\<^sub>p m) = (poly_map real) p ^\<^sub>p m"
  thus "poly_map real (p ^\<^sub>p n) = poly_map real p ^\<^sub>p n"
    apply(cases n)
    apply(simp_all)
    by (smt Suc_less_eq div2_less_self even_Suc odd_Suc_div_two poly_map_real_polymul)
qed

lemmas poly_map_real_polyarith = poly_map_real_polyadd poly_map_real_polyneg poly_map_real_polysub poly_map_real_polymul poly_map_real_polypow

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
    
lemma num_params_poly_map_real[simp]:
shows "num_params (poly_map real p) = num_params p"
by (induction p, simp_all)

lemma num_params_polyadd:
shows "num_params (p1 +\<^sub>p p2) \<le> max (num_params p1) (num_params p2)"
apply(induction p1 p2 rule: polyadd.induct)
apply(auto)[3]
proof-
  case (4 c n p c' n' p')
  show ?case
    apply(cases "n' < n")
    apply(simp)
    using 4
    apply(simp)
    apply(smt max.cobounded2 max.coboundedI2 max.commute max_def)
    apply(cases "n' = n")
    apply(simp add: Let_def)
    apply(smt "4.IH"(3) "4.IH"(4) le_max_iff_disj max.cobounded1)
    apply(simp)
    apply(safe)
    apply(simp_all)
    using 4(1) by auto
qed simp_all

lemma num_params_polyneg:
shows "num_params (~\<^sub>p p) = num_params p"
by (induction p rule: polyneg.induct) simp_all

lemma num_params_polymul:
shows "num_params (p1 *\<^sub>p p2) \<le> max (num_params p1) (num_params p2)"
apply(induction p1 p2 rule: polymul.induct)
apply(auto)[3]
proof-
  case (4 c n p c' n' p')
  show ?case
    apply(cases "n' < n")
    apply(simp)
    using 4
    apply(simp)
    apply(smt max.cobounded2 max.coboundedI2 max.commute max_def)
    apply(cases "n' > n")
    apply(simp add: Let_def)
    apply(safe)
    apply(simp_all)
    using 4(1)
    apply auto[1]
    using 4(2)
    apply(smt le_SucI le_neq_implies_less le_refl le_trans less_Suc_eq_le less_eq_Suc_le less_max_iff_disj less_not_refl linorder_neqE_nat max.absorb1 max.absorb2 max.assoc max.bounded_iff max.cobounded2 max.coboundedI1 max.coboundedI2 max.commute max.left_commute max.strict_order_iff max_less_iff_conj nat_le_linear not_less_eq_eq num_params.simps(8))
    using 4(3,4) num_params_polyadd[of "CN c n p *\<^sub>p c'" "CN 0\<^sub>p n (CN c n p *\<^sub>p p')"]
    apply(simp)
    by (smt max.commute max.left_commute max_def)
qed simp_all

lemma num_params_polypow:
shows "num_params (p ^\<^sub>p n) \<le> num_params p"
using assms
apply(induction n rule: polypow.induct)
apply(simp)
proof-
  fix v assume "(\<And>x. num_params (p ^\<^sub>p Suc v div 2) \<le> num_params p)"
  thus "num_params (p ^\<^sub>p Suc v) \<le> num_params p"
    unfolding polypow.simps
    apply(simp add: Let_def del: polypow.simps)
    apply(safe)
    apply(smt Suc_eq_plus1 add_self_div_2 dvd.order.trans evenE even_Suc even_Suc_div_two even_numeral max_def mult.commute mult_2 num_params_polymul oddE odd_Suc_div_two order.trans order_refl)
    by (smt even_Suc_div_two le_max_iff_disj max_def num_params_polymul)
qed

find_theorems "linorder_class.Max (_ \<union> _)"
find_theorems "0::nat" name: "induct"

lemma num_params_polynate:
shows "num_params (polynate p) \<le> num_params p"
proof(induction p rule: polynate.induct)
  case (2 l r)
  thus ?case
    using num_params_polyadd[of "polynate l" "polynate r"]
    by simp
next
  case (3 l r)
  thus ?case
    apply(simp add: polysub_def)
    using num_params_polyadd[of "polynate l" "~\<^sub>p (polynate r)"] 
    by (simp add: num_params_polyneg)
next
  case (4 l r)
  thus ?case
    using num_params_polymul[of "polynate l" "polynate r"]
    by simp
next
  case (5 p)
  thus ?case
    by (simp add: num_params_polyneg)
next
  case (6 p n)
  thus ?case
    using num_params_polypow[of n "polynate p"]
    by simp
qed simp_all

lemma polynate_poly_map_real[simp]:
fixes p :: "float poly"
shows "poly_map real (polynate p) = polynate (poly_map real p)"
by (induction p) (simp_all add: poly_map_real_polyarith)
                                      
(* Evaluating a float poly is equivalent to evaluating the corresponding
   real poly with the float parameters converted to reals. *)
lemma Ipoly_real_float_eqiv:
fixes p::"float poly" and xs::"float list"
assumes "num_params p \<le> length xs"
shows "Ipoly xs (p::real poly) = Ipoly xs p"
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

section \<open>Splitting polynomials to reduce floating point precision\<close>

(* TODO: Move this! Definitions regarding floating point numbers should not be in a theory about polynomials. *)
fun float_prec :: "float \<Rightarrow> int"
where "float_prec f = (let p=exponent f in if p \<ge> 0 then 0 else -p)"

fun float_round :: "nat \<Rightarrow> float \<Rightarrow> float"
where "float_round prec f = (
         let d = float_down prec f; u = float_up prec f
         in if f - d < u - f then d else u)"

lemma float_round_correct:
shows "float_prec (float_round prec f) \<le> prec"
apply(cases f)
apply(simp add: Let_def, safe)
thm float_down_correct
oops

(* Splits any polynomial p into two polynomials l, r, such that for all x::real. p(x) = l(x) + r(x)
   and all floating point coefficients in p are rounded to precision prec.
   Not all cases need to be give good results. Polynomials normalized with polynate
   only contain poly.C and poly.CN constructors. *)
fun split_by_prec :: "nat \<Rightarrow> float poly \<Rightarrow> float poly * float poly"
where "split_by_prec prec (poly.C f) = (let r = float_round prec f in (poly.C r, poly.C (f - r)))"
    | "split_by_prec prec (poly.Bound n) = (poly.Bound n, poly.C 0)"
    | "split_by_prec prec (poly.Add l r) = (let (ll, lr) = split_by_prec prec l;
                                                (rl, rr) = split_by_prec prec r
                                            in (poly.Add ll rl, poly.Add lr rr))"
    | "split_by_prec prec (poly.Sub l r) = (let (ll, lr) = split_by_prec prec l;
                                             (rl, rr) = split_by_prec prec r
                                         in (poly.Sub ll rl, poly.Sub lr rr))"
    | "split_by_prec prec (poly.Mul l r) = (let (ll, lr) = split_by_prec prec l;
                                                (rl, rr) = split_by_prec prec r
                                            in (poly.Mul ll rl, poly.Add (poly.Add (poly.Mul lr rl) (poly.Mul ll rr)) (poly.Mul lr rr)))"
    | "split_by_prec prec (poly.Neg p) = (let (l, r) = split_by_prec prec p in (poly.Neg l, poly.Neg r))"
    | "split_by_prec prec (poly.Pw p 0) = (poly.C 1, poly.C 0)"
    | "split_by_prec prec (poly.Pw p (Suc n)) = (let (l, r) = split_by_prec prec p in (poly.Pw l n, poly.Sub (poly.Pw p (Suc n)) (poly.Pw l n)))"
    | "split_by_prec prec (poly.CN c n p) = (let (cl, cr) = split_by_prec prec c;
                                                 (pl, pr) = split_by_prec prec p
                                             in (poly.CN cl n pl, poly.CN cr n pr))"

(* TODO: Prove precision constraint on l. *)
lemma split_by_prec_correct:
fixes args :: "real list"
assumes "(l, r) = split_by_prec prec p"
shows "Ipoly args p = Ipoly args l + Ipoly args r"
using assms
proof(induction p arbitrary: l r)
  case (Add p1 p2 l r)
  thus ?case by (simp add: Add(1,2)[OF pair_collapse] split_beta)
next
  case (Sub p1 p2 l r)
  thus ?case by (simp add: Sub(1,2)[OF pair_collapse] split_beta)
next
  case (Mul p1 p2 l r)
  thus ?case by (simp add: Mul(1,2)[OF pair_collapse] split_beta algebra_simps)
next
  case (Neg p l r) 
  thus ?case by (simp add: Neg(1)[OF pair_collapse] split_beta)
next
  case (Pw p n l r)
  thus ?case by (cases n) (simp_all add: Pw(1)[OF pair_collapse] split_beta)
next
  case (CN c n p2)
  thus ?case by (simp add: CN(1,2)[OF pair_collapse] split_beta algebra_simps)
qed (simp_all add: Let_def)

section \<open>Splitting polynomials by degree\<close>

fun maxdegree :: "('a::zero) poly \<Rightarrow> nat"
where "maxdegree (poly.C c) = 0"
    | "maxdegree (poly.Bound n) = 1"
    | "maxdegree (poly.Add l r) = max (maxdegree l) (maxdegree r)"
    | "maxdegree (poly.Sub l r) = max (maxdegree l) (maxdegree r)"
    | "maxdegree (poly.Mul l r) = maxdegree l + maxdegree r"
    | "maxdegree (poly.Neg p) = maxdegree p"
    | "maxdegree (poly.Pw p n) = n * maxdegree p"
    | "maxdegree (poly.CN c n p) = max (maxdegree c) (1 + maxdegree p)"

fun split_by_degree :: "nat \<Rightarrow> 'a::zero poly \<Rightarrow> 'a poly * 'a poly"
where "split_by_degree n (poly.C c) = (poly.C c, poly.C 0)"
    | "split_by_degree 0 p = (poly.C 0, p)"
    | "split_by_degree (Suc n) (poly.CN c v p) = (
         let (cl, cr) = split_by_degree (Suc n) c;
             (pl, pr) = split_by_degree n p
         in (poly.CN cl v pl, poly.CN cr v pr))"
    (* This function is only intended for use on polynomials in normal form.
       Hence most cases never get executed. *)
    | "split_by_degree n p = (poly.C 0, p)"

lemma split_by_degree_correct:
fixes x :: "real list" and p :: "float poly"
assumes "(l, r) = split_by_degree n p"
shows "maxdegree l \<le> n" (is ?P1)
and   "Ipoly x p = Ipoly x l + Ipoly x r" (is ?P2)
and   "num_params l \<le> num_params p" (is ?P3)
and   "num_params r \<le> num_params p" (is ?P4)
proof-
  have proposition: "?P1 \<and> ?P2 \<and> ?P3 \<and> ?P4"
  using assms
  proof(induction p arbitrary: l r n)
    case (C c l r n)
    thus ?case by simp
  next
    case (Bound v l r n)
    thus ?case by (cases n) simp_all
  next
    case (Add p1 p2 l r n)
    thus ?case by (cases n) simp_all
  next
    case (Sub p1 p2 l r n)
    thus ?case by (cases n) simp_all
  next
    case (Mul p1 p2 l r n)
    thus ?case by (cases n) simp_all
  next
    case (Neg p l r n)
    thus ?case by (cases n) simp_all
  next
    case (Pw p k l r n)
    thus ?case by (cases n) simp_all
  next
    case (CN c v p l r n)
    show ?case
    proof(cases n)
      case 0
      thus ?thesis using CN by simp
    next
      case (Suc m)
      obtain cl cr where cl_cr_def: "(cl, cr) = split_by_degree (Suc m) c"
        by (cases "split_by_degree (Suc m) c", simp)
      obtain pl pr where pl_pr_def: "(pl, pr) = split_by_degree m p"
        by (cases "split_by_degree m p", simp)
      have [simp]: "Ipoly x p = Ipoly x pl + Ipoly x pr"
        using CN(2)[OF pl_pr_def]
        by (cases n) simp_all
      from CN(3)
      have l_decomp: "l = CN cl v pl" and r_decomp: "r = CN cr v pr"
        by (simp_all add: Suc cl_cr_def[symmetric] pl_pr_def[symmetric])
      show ?thesis
        apply(simp add: l_decomp, safe)
        using CN(1)[OF cl_cr_def]
        apply(simp add: Suc)
        using CN(2)[OF pl_pr_def]
        apply(simp add: Suc)
        using pl_pr_def
        apply(cases p)
        apply(simp_all)
        apply(simp_all add: l_decomp r_decomp CN(1)[OF cl_cr_def] algebra_simps)
        apply(safe)
        prefer 3
        using CN(1)[OF cl_cr_def] 
        apply(simp_all add: max.coboundedI1)[2]
        using CN(2)[OF pl_pr_def]
        by auto
    qed
  qed
  
  show ?P1 using proposition by simp
  show ?P2 using proposition by simp
  show ?P3 using proposition by simp
  show ?P4 using proposition by simp
qed

end
