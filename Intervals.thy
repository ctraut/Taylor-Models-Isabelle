theory Intervals
imports "~~/src/HOL/Library/Float"
        "~~/src/HOL/Library/Set_Algebras"
begin

(* I define my own interval type here. I then define the basic arithmetic operations on intervals. 
   This way, I can define and evaluate interval polynomials. *)
typedef (overloaded) 'a interval = "{(a::'a::order, b). a \<le> b}"
  by auto

setup_lifting type_definition_interval

lift_definition Ivl::"'a::order \<Rightarrow> 'a \<Rightarrow> 'a interval"
is "\<lambda>a b. (a, max a b)"
  by (simp add: max_def)

lift_definition proc_of::"'a::order interval \<Rightarrow> 'a \<times> 'a"
is Rep_interval .
  
lift_definition lower::"('a::order) interval \<Rightarrow> 'a" is fst .
lift_definition upper::"('a::order) interval \<Rightarrow> 'a" is snd .

definition width :: "'a::{order,minus} interval \<Rightarrow> 'a"
where "width i = upper i - lower i"

definition mid :: "float interval \<Rightarrow> float"
where "mid i = (lower i + upper i) * Float 1 (-1)"

definition set_of :: "'a::order interval \<Rightarrow> 'a set"
where "set_of i = {lower i..upper i}"

definition interval_of :: "'a::order \<Rightarrow> 'a interval"
where "interval_of x = Ivl x x"

definition interval_map :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a interval \<Rightarrow> 'b interval"
where "interval_map f i = Ivl (f (lower i)) (f (upper i))"

definition interval_union :: "'a::order interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
where "interval_union a b = Ivl (min (lower a) (lower b)) (max (upper a) (upper b))"

fun interval_list_union :: "'a::linorder interval list \<Rightarrow> 'a interval"
where "interval_list_union [] = undefined"
    | "interval_list_union [I] = I"
    | "interval_list_union (I#Is) = interval_union I (interval_list_union Is)"

lemmas [simp] = proc_of_def

lemma lower_le_upper:
shows "lower i \<le> upper i"
proof-
  obtain y where i_def: "i = Abs_interval y" and y_def: "y \<in> {(a, b). a \<le> b}"
    using Abs_interval_cases by auto
  hence "fst y \<le> snd y"
    by auto
  thus ?thesis
    by (simp add: i_def interval.Abs_interval_inverse[OF y_def] lower_def upper_def)
qed

lemma lower_Ivl[simp]:
shows "lower (Ivl a b) = a"
by (simp add: Ivl.rep_eq lower.rep_eq)

lemma upper_Ivl_a[simp]:
assumes "b \<le> a"
shows "upper (Ivl a b) = a"
using assms
by (simp add: upper_def Ivl.rep_eq max_def)

lemma upper_Ivl_b[simp]:
assumes "a \<le> b"
shows "upper (Ivl a b) = b"
using assms
by (simp add: upper_def Ivl.rep_eq max_def)

lemma lower_refl[simp]:
shows "lower (Ivl a a) = a"
by (simp add: Ivl.rep_eq lower.rep_eq)

lemma upper_refl[simp]:
shows "upper (Ivl a a) = a"
by (simp add: Ivl.rep_eq max_def upper.rep_eq)

lemma upper_Ivl_upper_lower[simp]:
shows "upper (Ivl (lower I) (upper I)) = upper I"
using lower_le_upper upper_Ivl_b
by auto

lemma upper_Ivl_upper_lower_real[simp]:
fixes I::"float interval"
shows "upper (Ivl (real_of_float (lower I)) (real_of_float(upper I))) = real_of_float (upper I)"
using lower_le_upper less_eq_float.rep_eq upper_Ivl_b
by blast

lemma set_of_interval_union:
fixes A::"'a::linorder interval"
shows "set_of A \<union> set_of B \<subseteq> set_of (interval_union A B)"
by (auto simp add: min_def max_def set_of_def interval_union_def)

lemma interval_union_commute:
fixes A::"'a::linorder interval"
shows "interval_union A B = interval_union B A"
by (auto simp add: min_def max_def set_of_def interval_union_def)

lemma interval_union_mono1:
fixes A :: "'a::linorder interval"
shows "set_of a \<subseteq> set_of (interval_union a A)"
by (auto simp add: set_of_def interval_union_def min_def max_def)

lemma interval_union_mono2:
fixes A :: "'a::linorder interval"
shows "set_of A \<subseteq> set_of (interval_union a A)"
by (auto simp add: set_of_def interval_union_def min_def max_def)

lemma interval_exhaust:
obtains l u
where "(i::'a::order interval) = Ivl l u"
and   "l \<le> u"
by (metis Ivl.abs_eq Rep_interval_inverse lower.rep_eq lower_le_upper max_absorb2 prod.swap_def swap_simp swap_swap upper.rep_eq)

(* Definitions that make some common assumptions about lists of intervals easier to write. *)
definition all_in :: "'a::order list \<Rightarrow> 'a interval list \<Rightarrow> bool"
(infix "(all'_in)" 50)
where "x all_in I = (length x = length I \<and> (\<forall>i < length I. x!i \<in> set_of (I!i)))"

definition all_subset :: "'a::order interval list \<Rightarrow> 'a interval list \<Rightarrow> bool"
(infix "(all'_subset)" 50)
where "I all_subset J = (length I = length J \<and> (\<forall>i < length I. set_of (I!i) \<subseteq> set_of (J!i)))"

lemmas [simp] = all_in_def all_subset_def

lemma mid_in_interval:
shows "mid i \<in> set_of i"
proof-
  obtain l u where i_def: "i = Ivl l u" and "l \<le> u" using interval_exhaust by blast
  
  {
    have "real_of_float l * Float 1 1  \<le> (real_of_float l + real_of_float u)"
      using `l \<le> u` by (simp add: Float.compute_float_one Float.compute_float_times)
    hence "real_of_float l * (Float 1 1 * Float 1 (-1)) \<le> (real_of_float l + real_of_float u) * Float 1 (-1)"
      by simp 
    hence "real_of_float l \<le> (real_of_float l + real_of_float u) * Float 1 (- 1)"
      by (simp add: Float.compute_float_one Float.compute_float_times)
  }
  moreover
  {
    have "(real_of_float l + real_of_float u) \<le> real_of_float u * Float 1 1 "
      using `l \<le> u` by (simp add: Float.compute_float_one Float.compute_float_times)
    hence "(real_of_float l + real_of_float u) * Float 1 (-1) \<le> real_of_float u * (Float 1 1 * Float 1 (-1))"
      by simp
    hence "(real_of_float l + real_of_float u) * Float 1 (- 1) \<le> real_of_float u"
      by (simp add: Float.compute_float_one Float.compute_float_times)
  }
  ultimately show ?thesis
    by (simp add: i_def set_of_def mid_def)
qed

lemma all_subsetD:
assumes "I all_subset J"
assumes "x all_in I"
shows "x all_in J"
using assms
by (auto, auto)

instantiation "interval" :: ("{order,equal}") equal
begin
  definition "equal_class.equal a b \<equiv> (lower a = lower b) \<and> (upper a = upper b)"
  instance
  apply(standard)
  apply(simp add: equal_interval_def)
  by (smt interval_exhaust lower_Ivl upper_Ivl_b)
end

(* Arithmetic on intervals. *)
instantiation "interval" :: ("{order,plus}") plus
begin
  definition "a + b = Ivl (lower a + lower b) (upper a + upper b)"
  instance ..
end
instantiation "interval" :: ("{order,minus}") minus
begin
  definition "a - b = Ivl (lower a - upper b) (upper a - lower b)"
  instance ..
end
instantiation "interval" :: ("{order,uminus}") uminus
begin
  definition "-a = Ivl (-upper a) (-lower a)"
  instance ..
end
instantiation "interval" :: ("{times,order}") times
begin
definition "a * b = Ivl (min (min (lower a * lower b) (upper a * lower b)) 
                             (min (lower a * upper b) (upper a * upper b)))
                        (max (max (lower a * lower b) (upper a * lower b)) 
                             (max (lower a * upper b) (upper a * upper b)))"
instance ..
end
instantiation "interval" :: ("{order,zero}") zero
begin
  definition "0 = Ivl 0 0"
  instance ..
end
instantiation "interval" :: ("{order,one}") one
begin
  definition "1 = Ivl 1 1"
  instance ..
end
instantiation "interval" :: ("{order,inverse}") inverse
begin
  definition "inverse a = Ivl (min (inverse (lower a)) (inverse (upper a))) (max (inverse (lower a)) (inverse (upper a)))"
  instance ..
end
instantiation "interval" :: ("{order,times,one}") power
begin
  instance ..
end

instantiation "interval" :: (linordered_idom) comm_monoid_add
begin
  instance
  proof
    fix a b c::"'a interval"
    show "a + b + c = a + (b + c)"
      apply(cases a rule: interval_exhaust, cases b rule: interval_exhaust, cases c rule: interval_exhaust)
      by (simp add: plus_interval_def algebra_simps)
  next
    fix a b::"'a interval"
    show "a + b = b + a"
      by (simp add: plus_interval_def algebra_simps)
  next
    fix a::"'a interval"
    show "0 + a = a"
      by (cases a rule: interval_exhaust, simp add: plus_interval_def zero_interval_def)
  qed
end

instantiation "interval" :: (linordered_idom) cancel_semigroup_add
begin
  instance
  proof
    fix a b c::"'a interval"
    assume "a + b = a + c"
    thus "b = c"
      apply(cases a rule: interval_exhaust, cases b rule: interval_exhaust, cases c rule: interval_exhaust)
      apply(simp add: plus_interval_def)
      by (metis add.commute add_mono add_right_imp_eq lower_Ivl upper_Ivl_b)
  next
    
    fix a b c::"'a interval"
    assume "b + a = c + a"
    thus "b = c"
      apply(cases a rule: interval_exhaust, cases b rule: interval_exhaust, cases c rule: interval_exhaust)
      apply(simp add: plus_interval_def)
      by (metis add_mono_thms_linordered_semiring(1) add_right_cancel lower_Ivl upper_Ivl_b)
  qed
end

fun centered :: "float interval \<Rightarrow> float interval"
where "centered i = i - interval_of (mid i)"

lemma interval_mul_commute:
fixes A :: "'a::linordered_idom interval"
shows "A * B = B * A"
by (simp add: times_interval_def min.commute min.left_commute max.commute max.left_commute mult.commute)

lemma interval_times_zero_right[simp]:
fixes A :: "'a::linordered_idom interval"
shows "A * 0 = 0"
by (simp add: times_interval_def zero_interval_def)

lemma interval_times_zero_left[simp]:
fixes A :: "'a::linordered_idom interval"
shows "0 * A = 0"
by (simp add: times_interval_def zero_interval_def)

lemma one_times_ivl_left[simp]:
fixes A :: "'a::linordered_idom interval"
shows "1 * A = A"
by (cases A rule: interval_exhaust, auto simp: times_interval_def one_interval_def min_def max_def)

lemma one_times_ivl_right[simp]:
fixes A :: "'a::linordered_idom interval"
shows "A * 1 = A"
using one_times_ivl_left[OF assms, unfolded interval_mul_commute]
by assumption

lemma set_of_real_to_float[simp]:
fixes A :: "float interval"
shows "(real_of_float a \<in> set_of (interval_map real_of_float A)) = (a \<in> set_of A)"
by (cases A rule: interval_exhaust, simp add: set_of_def interval_map_def)

(* Coercions on intervals. *)
lemmas [simp] = interval_of_def

declare [[coercion "interval_of :: float \<Rightarrow> float interval"]]
declare [[coercion "interval_of :: real \<Rightarrow> real interval"]]
declare [[coercion_map interval_map]]

(* Coercion of a "float interval" to a "real interval" is homomorph. *)
lemma interval_map_real_add[simp]:
fixes i1::"float interval"
shows "interval_map real_of_float (i1 + i2) = interval_map real_of_float i1 + interval_map real_of_float i2"
by (cases i1 rule: interval_exhaust, cases i2 rule: interval_exhaust, simp add: plus_interval_def interval_map_def)

lemma interval_map_real_sub[simp]:
fixes i1::"float interval"
shows "interval_map real_of_float (i1 - i2) = interval_map real_of_float i1 - interval_map real_of_float i2"
by (cases i1 rule: interval_exhaust, cases i2 rule: interval_exhaust, simp add: minus_interval_def interval_map_def)

lemma interval_map_real_neg[simp]:
fixes i::"float interval"
shows "interval_map real_of_float (-i) = - interval_map real_of_float i"
by (cases i rule: interval_exhaust, simp add: uminus_interval_def interval_map_def)

lemma interval_map_real_mul[simp]:
fixes i1::"float interval"
shows "interval_map real_of_float (i1 * i2) = interval_map real_of_float i1 * interval_map real_of_float i2"
by (cases i1 rule: interval_exhaust, cases i2 rule: interval_exhaust, simp add: times_interval_def real_of_float_max real_of_float_min interval_map_def)

lemma interval_map_real_pow[simp]:
fixes i::"float interval"
shows "interval_map real_of_float (i ^ n) = interval_map real_of_float i ^  n"
apply(cases i rule: interval_exhaust, induction n)
using interval_map_real_mul by (auto simp: one_interval_def interval_map_def)

lemma interval_map_real_Ivl[simp]:
fixes l::float and u::float
shows "interval_map real_of_float (Ivl l u) = Ivl (real_of_float l) (real_of_float u)"
apply(simp add: interval_map_def)
by (metis interval_exhaust less_eq_float.rep_eq lower_Ivl max.cobounded2 max_def upper_Ivl_a upper_Ivl_b)

(* Operations on intervals are monotone. *)
lemma set_of_add_mono:
fixes a :: "'a::ordered_ab_group_add"
assumes "a \<in> set_of A"
assumes "b \<in> set_of B"
shows "a + b \<in> set_of (A + B)"
apply(cases A rule: interval_exhaust, cases B rule: interval_exhaust)
using assms
by (simp add: set_of_def plus_interval_def add_mono)

lemma set_of_minus_mono:
fixes a :: "'a::ordered_ab_group_add"
assumes "a \<in> set_of A"
assumes "b \<in> set_of B"
shows "a - b \<in> set_of (A - B)"
apply(cases A rule: interval_exhaust, cases B rule: interval_exhaust)
using assms
by (simp add: minus_interval_def set_of_def diff_mono)

lemma set_of_uminus_mono:
fixes a :: "'a::ordered_ab_group_add"
assumes "a \<in> set_of A"
shows "-a \<in> set_of (-A)"
apply(cases A rule: interval_exhaust)
using assms
by (simp add: uminus_interval_def set_of_def)

lemma set_of_mult_mono:
fixes a :: "'a::linordered_idom"
assumes "a \<in> set_of A"
assumes "b \<in> set_of B"
shows "a * b \<in> set_of (A * B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" and lea: "la \<le> ua" using interval_exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" and leb: "lb \<le> ub" using interval_exhaust by auto
  have a_def: "a \<in> {la..ua}" using assms(1) lea by (simp add: A_def set_of_def)
  have b_def: "b \<in> {lb..ub}" using assms(2) leb by (simp add: B_def set_of_def)
    
  have ineqs: "la \<le> a" "a \<le> ua" "lb \<le> b" "b \<le> ub"
    using a_def b_def
    by auto
  hence ineqs': "-a \<le> -la" "-ua \<le> -a" "-b \<le> -lb" "-ub \<le> -b"
    by(simp_all)
  
  show ?thesis
    using mult_mono[OF ineqs(1) ineqs(3), simplified]
          mult_mono'[OF ineqs(2) ineqs'(3), simplified]
          mult_mono'[OF ineqs'(1) ineqs(4), simplified]
          mult_mono[OF ineqs'(2) ineqs'(4), simplified]
          mult_mono[OF ineqs'(1) ineqs'(3), simplified]
          mult_mono'[OF ineqs'(2) ineqs(3), simplified]
          mult_mono'[OF ineqs(1) ineqs'(4), simplified]
          mult_mono[OF ineqs(2) ineqs(4), simplified]
          lea leb
    apply(simp add: A_def B_def times_interval_def set_of_def min_le_iff_disj le_max_iff_disj, safe)
    by (smt ineqs(1) ineqs(2) le_less not_le order_trans zero_le_mult_iff)+
qed

lemma [simp]: "(x::'a::order) \<in> set_of (Ivl x x)"
  by (simp add: set_of_def)

lemma set_of_power_mono:
fixes a :: "'a::linordered_idom"
assumes "a \<in> set_of A"
shows "a^n \<in> set_of (A^n)"
using assms
by (induction n, simp_all add: set_of_mult_mono one_interval_def)

(* TODO: Clean this proof up! *)
lemma set_of_add_distrib:
fixes A :: "'a::linordered_idom interval"
shows "set_of A + set_of B = set_of (A + B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" and lea: "la \<le> ua" using interval_exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" and leb: "lb \<le> ub" using interval_exhaust by auto
  from assms
  show ?thesis
    using lea leb
    apply(simp add: A_def B_def plus_interval_def set_plus_def)
    apply(rule)
    apply(rule)
    apply(safe)
    apply(simp_all add: add_mono set_of_def)
    apply(safe)
    proof(goal_cases)
      case (1 x)
      def wa\<equiv>"ua - la"
      def wb\<equiv>"ub - lb"
      def w\<equiv>"wa + wb"
      def d\<equiv>"x - la - lb"
      have "0 \<le> wa" using 1 by (simp add: wa_def)
      have "0 \<le> wb" using 1 by (simp add: wb_def)
      have "0 \<le> w" using 1 by (simp add: w_def wa_def wb_def)
      hence "0 \<le> d" using 1 by (simp add: d_def)
      have "d \<le> w" using 1 by (simp add: d_def w_def wa_def wb_def)
      hence "d \<le> wa + wb" by (simp add: w_def)
      
      show ?case
      apply(cases "wa \<le> wb")
      proof-
        case True
        def da\<equiv>"max 0 (min wa (d - wa))"
        def db\<equiv>"d - da"
        
        have d_decomp: "d = da + db"
          by (simp add: da_def db_def)
        have "x = d + la + lb"
          by (simp add: d_def)
        also have "... =  (la + da) + (lb + db)"
          by (simp add: d_decomp)
        finally have x_decomp: "x = (la + da) + (lb + db)" .
        show "\<exists>a\<in>{la..ua}. \<exists>b\<in>{lb..ub}. x = a + b"
          apply(rule)+
          apply(rule x_decomp)
          apply(simp)
          apply(safe)
          using `0 \<le> d` d_decomp da_def apply linarith
          using True `d \<le> wa + wb` d_decomp da_def wb_def apply linarith
          apply(simp, safe)
          apply (simp add: da_def)
          using "1"(1) da_def wa_def by auto
      next
        case False
        def db\<equiv>"max 0 (min wb (d - wb))"
        def da\<equiv>"d - db"
        
        have d_decomp: "d = da + db"
          by (simp add: da_def db_def)
        have "x = d + la + lb"
          by (simp add: d_def)
        also have "... =  (la + da) + (lb + db)"
          by (simp add: d_decomp)
        finally have x_decomp: "x = (la + da) + (lb + db)" .
        
        show "\<exists>a\<in>{la..ua}. \<exists>b\<in>{lb..ub}. x = a + b"
          apply(rule)+
          apply(rule x_decomp)
          apply(simp, safe)
          using db_def apply auto[1]
          using "1"(2) db_def wb_def apply auto[1]
          apply(simp, safe)
          using `0 \<le> d` da_def db_def apply auto[1]
          using False `d \<le> wa + wb` d_decomp db_def wa_def by linarith
      qed
    qed
qed

lemma set_of_add_cong:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A = set_of A'"
assumes "set_of B = set_of B'"
shows "set_of (A + B) = set_of (A' + B')"
by (simp add: set_of_add_distrib[symmetric] assms)

lemma set_of_add_inc_left:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A + B) \<subseteq> set_of (A' + B)"
by (simp add: set_of_add_distrib[symmetric] set_plus_mono2[OF assms])

lemma set_of_add_inc_right:
fixes A :: "'a::linordered_idom interval"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A + B) \<subseteq> set_of (A + B')"
using set_of_add_inc_left[OF assms]
by (simp add: add.commute)

lemma set_of_add_inc:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A + B) \<subseteq> set_of (A' + B')"
using set_of_add_inc_left[OF assms(1)] set_of_add_inc_right[OF assms(2)]
by auto

lemma set_of_neg_inc:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (-A) \<subseteq> set_of (-A')"
apply(cases A rule: interval_exhaust, cases A' rule: interval_exhaust)
using assms by (simp add: uminus_interval_def set_of_def)

lemma set_of_sub_inc_left:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A - B) \<subseteq> set_of (A' - B)"
apply(cases A rule: interval_exhaust, cases B rule: interval_exhaust, cases A' rule: interval_exhaust)
using assms by (simp add: uminus_interval_def minus_interval_def plus_interval_def set_of_def)

lemma set_of_sub_inc_right:
fixes A :: "'a::linordered_idom interval"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A - B) \<subseteq> set_of (A - B')"
apply(cases A rule: interval_exhaust, cases B rule: interval_exhaust, cases B' rule: interval_exhaust)
using assms by (simp add: uminus_interval_def minus_interval_def plus_interval_def set_of_def)

lemma set_of_sub_inc:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A - B) \<subseteq> set_of (A' - B')"
using set_of_sub_inc_left[OF assms(1)] set_of_sub_inc_right[OF assms(2)]
by auto

lemma set_of_distrib_right:
fixes A1 :: "'a::linordered_idom interval"
shows "set_of ((A1 + A2) * B) \<subseteq> set_of (A1 * B + A2 * B)"
proof
  fix x assume assm: "x \<in> set_of ((A1 + A2) * B)"
  
  obtain la1 ua1 where A1_def: "A1 = Ivl la1 ua1" and lea1: "la1 \<le> ua1" using interval_exhaust by auto
  obtain la2 ua2 where A2_def: "A2 = Ivl la2 ua2" and lea2: "la2 \<le> ua2" using interval_exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" and leb: "lb \<le> ub" using interval_exhaust by auto
  
  from assm
  have a1: "min (min ((la1 + la2) * lb) ((ua1 + ua2) * lb)) (min ((la1 + la2) * ub) ((ua1 + ua2) * ub)) \<le> x"
  and  a2: "x \<le> max (max ((la1 + la2) * lb) ((ua1 + ua2) * lb)) (max ((la1 + la2) * ub) ((ua1 + ua2) * ub))"
    using lea1 lea2 leb
    by (auto simp: A1_def A2_def B_def times_interval_def plus_interval_def set_of_def)
    
  show "x \<in> set_of (A1 * B + A2 * B)"
    using lea1 lea2 leb
    apply(simp add: A1_def A2_def B_def times_interval_def plus_interval_def set_of_def)
    apply(rule conjI[OF order.trans[OF _ a1]  order.trans[OF a2]])
    apply(smt add_mono distrib_right dual_order.trans min.cobounded1 min_def)
    apply(subst upper_Ivl_b)
    apply(simp add: add_mono max.left_commute min_le_iff_disj)
    apply(smt add_mono distrib_right dual_order.trans max.cobounded2 max_def)
    done
qed

lemma set_of_mul_inc_left:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A * B) \<subseteq> set_of (A' * B)"
proof
  fix x assume x_def: "x \<in> set_of (A * B)"

  obtain la ua where A_def: "A = Ivl la ua" and lea: "la \<le> ua" using interval_exhaust by auto
  obtain la' ua' where A'_def: "A' = Ivl la' ua'" and lea': "la' \<le> ua'" using interval_exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" and leb: "lb \<le> ub" using interval_exhaust by auto
  
  from x_def assms lea lea' leb
  show "x \<in> set_of (A' * B)"
    apply(simp add: A_def A'_def B_def times_interval_def set_of_def)
    apply(safe)
    apply(smt min.absorb_iff2 min.coboundedI2 min_def mult_le_cancel_right)
    by (smt lea lea' leb max_def max_mult_distrib_right min_def min_le_iff_disj mult_compare_simps(1) order_antisym_conv order_trans)
qed

lemma set_of_mul_inc_right:
fixes A :: "'a::linordered_idom interval"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A * B) \<subseteq> set_of (A * B')"
unfolding interval_mul_commute[of A]
by (rule set_of_mul_inc_left[OF assms])

lemma set_of_mul_inc:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A * B) \<subseteq> set_of (A' * B')" 
using set_of_mul_inc_right[OF assms(2)] set_of_mul_inc_left[OF assms(1)]
by auto

lemma set_of_pow_inc:
fixes A :: "'a::linordered_idom interval"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A^n) \<subseteq> set_of (A'^n)"
using assms
by (induction n, simp_all add: set_of_mul_inc)

lemma set_of_distrib_left:
fixes A1 :: "'a::linordered_idom interval"
shows "set_of (B * (A1 + A2)) \<subseteq> set_of (B * A1 + B * A2)"
unfolding interval_mul_commute
by (rule set_of_distrib_right[unfolded interval_mul_commute])

lemma set_of_distrib_right_left:
fixes A1 :: "'a::linordered_idom interval"
shows "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * B1 + A1 * B2 + A2 * B1 + A2 * B2)"
proof-
  have "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * (B1 + B2) + A2 * (B1 + B2))"
    by (rule set_of_distrib_right)
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + A2 * (B1 + B2))"
    by (rule set_of_add_inc_left[OF set_of_distrib_left])
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + (A2 * B1 + A2 * B2))"
    by (rule set_of_add_inc_right[OF set_of_distrib_left])
  finally show ?thesis
    by (simp add: add.assoc)
qed

lemma set_of_mul_contains_zero:
fixes A :: "'a::linordered_idom interval"
assumes "0 \<in> set_of A \<or> 0 \<in> set_of B"
shows "0 \<in> set_of (A * B)"
using assms
apply(cases A rule: interval_exhaust, cases B rule: interval_exhaust)
apply(simp add: times_interval_def set_of_def)
apply(safe)
apply(metis (no_types, hide_lams) eq_iff min_le_iff_disj mult_zero_left mult_zero_right zero_le_mult_iff)
apply(metis le_max_iff_disj mult_zero_right order_refl zero_le_mult_iff)
apply(metis linear min.coboundedI1 min.coboundedI2 mult_nonneg_nonpos mult_nonpos_nonneg)
apply(metis linear max.coboundedI1 max.coboundedI2 mult_nonneg_nonneg mult_nonpos_nonpos)
done

(* Subdivisions on intervals and interval vectors. *)
fun subdivide_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval list"
where "subdivide_interval 0 I = [I]"
    | "subdivide_interval (Suc n) I = (
         let m = mid I
         in (subdivide_interval n (Ivl (lower I) m)) @ (subdivide_interval n (Ivl m (upper I)))
       )"

fun split_domain :: "(float interval \<Rightarrow> float interval list) \<Rightarrow> float interval list \<Rightarrow> float interval list list"
where "split_domain split [] = [[]]"
    | "split_domain split (I#Is) = (
         let S = split I;
             D = split_domain split Is
         in concat (map (\<lambda>d. map (\<lambda>s. s # d) S) D)
       )"

lemma subdivide_interval_length:
shows "length (subdivide_interval n I) = 2^n"
by(induction n arbitrary: I, simp_all add: Let_def)

lemma subdivide_interval_correct:
fixes x :: real
assumes "x \<in> set_of I"
shows "list_ex (\<lambda>i. x \<in> set_of i) (subdivide_interval n I)"
using assms
apply(induction n arbitrary: x I)
apply(simp_all add: Let_def  list_ex_iff)
(* TODO: better proof. *)
by (metis UnCI atLeastAtMost_iff interval_map_def le_cases lower_Ivl mid_in_interval set_of_def upper_Ivl_b upper_Ivl_upper_lower_real)

lemma split_domain_correct:
fixes x :: "real list"
assumes "x all_in I"
assumes split_correct: "\<And>(x::real) (a::float) I. x \<in> set_of I \<Longrightarrow> list_ex (\<lambda>i::float interval. x \<in> set_of i) (split I)"
shows "list_ex (\<lambda>s. x all_in s) (split_domain split I)"
using assms(1)
proof(induction I arbitrary: x)
  case (Cons I Is x)
  have "x \<noteq> []"
    using Cons(2) by auto
  obtain x' xs where x_decomp: "x = x' # xs"
    using \<open>x \<noteq> []\<close> list.exhaust by auto
  hence "x' \<in> set_of I" "xs all_in Is"
    using Cons(2)
    by auto
  show ?case
    using Cons(1)[OF \<open>xs all_in Is\<close>]
          split_correct[OF \<open>x' \<in> set_of I\<close>]
    apply(simp add: list_ex_iff set_of_def)
    by (smt length_Cons less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc x_decomp)
qed simp

lemma split_domain_nonempty:
assumes "\<And>I. split I \<noteq> []"
shows "split_domain split I \<noteq> []"
using last_in_set assms
by (induction I, auto)

lemma interval_list_union_correct:
assumes "S \<noteq> []"
assumes "i < length S"
shows "set_of (S!i) \<subseteq> set_of (interval_list_union S)"
using assms
proof(induction S arbitrary: i)
  case (Cons a S i)
  thus ?case
    proof(cases S)
      fix b S'
      assume "S = b # S'"
      hence "S \<noteq> []"
        by simp
      show ?thesis
      proof(cases i)
        case 0
        show ?thesis
          apply(cases S)
          using interval_union_mono1
          by (auto simp add: 0)
      next
        case (Suc i_prev)
        hence "i_prev < length S"
        using Cons(3) by simp
        
        from Cons(1)[OF \<open>S \<noteq> []\<close> this] Cons(1)
        have "set_of ((a # S) ! i) \<subseteq> set_of (interval_list_union S)"
          by (simp add: \<open>i = Suc i_prev\<close>)
        also have "... \<subseteq> set_of (interval_list_union (a # S))"
          using \<open>S \<noteq> []\<close>
          apply(cases S)
          using interval_union_mono2
          by auto
        finally show ?thesis .
      qed
    qed simp
qed simp

(* Rounding of float intervals, by increasing their width. *)
fun round_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> float interval"
where "round_ivl prec i = Ivl (float_down prec (lower i)) (float_up prec (upper i))"

lemma float_down_le:
shows "float_down p f \<le> f"
using round_down by simp

lemma float_up_le:
shows "f \<le> float_up p f"
using round_up by simp

lemma round_ivl_correct:
shows "set_of A \<subseteq> set_of (round_ivl prec A)"
proof(cases A rule: interval_exhaust, rule)
  fix l u x
  assume A_decomp: "A = Ivl l u"
  and "l \<le> u"
  and "x \<in> set_of A"
  hence "l \<le> x" and "x \<le> u"
    by (simp_all add: set_of_def)
    
  have "float_down prec l \<le> x"
    by (rule order.trans[OF float_down_le \<open>l \<le> x\<close>])
  moreover have "x \<le> float_up prec u"
    by (rule order.trans[OF \<open>x \<le> u\<close> float_up_le])
  ultimately show "x \<in> set_of (round_ivl prec A)"
    using \<open>l \<le> u\<close> by (simp add: A_decomp set_of_def)
qed


lemma real_of_float_round_ivl_correct:
shows "set_of A \<subseteq> set_of ((round_ivl prec A) :: real interval)"
proof(rule)
  fix x :: real
  assume "x \<in> set_of A"
  obtain l u where A_decomp: "A = Ivl l u" and "l \<le> u"
    using interval_exhaust by blast
  from \<open>x \<in> set_of A\<close> \<open>l \<le> u\<close>
  have "l \<le> x" "x \<le> u"
    by (auto simp add: set_of_def A_decomp)
  hence "round_down prec l \<le> l"
    and "u \<le> round_up prec u"
    using round_ivl_correct[of A prec] \<open>l \<le> u\<close> round_up 
    by (auto simp add: A_decomp set_of_def) 
  thus "x \<in> set_of (round_ivl prec A)"
    using \<open>l \<le> x\<close> \<open>x \<le> u\<close>
    by (simp add: set_of_def A_decomp)
qed

end