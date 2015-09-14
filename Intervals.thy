theory Intervals
imports "~~/src/HOL/Library/Float"
        "~~/src/HOL/Library/Set_Algebras"
begin

(* I define my own interval type here. I then define the basic arithmetic operations on the intervals. 
   This way, I can define and evaluate polynomials over the set of intervals. *)
datatype 'a interval = Ivl 'a 'a

primrec lower :: "'a interval \<Rightarrow> 'a"
where "lower (Ivl l u) = l"

primrec upper :: "'a interval \<Rightarrow> 'a"
where "upper (Ivl l u) = u"

primrec mid :: "float interval \<Rightarrow> float"
where "mid (Ivl l u) = (l + u) * Float 1 (-1)"

primrec proc_of :: "'a interval \<Rightarrow> 'a \<times> 'a"
where "proc_of (Ivl l u) = (l, u)"

primrec set_of :: "('a::order) interval \<Rightarrow> 'a set"
where "set_of (Ivl l u) = {l..u}"

definition interval_of :: "'a \<Rightarrow> 'a interval"
where "interval_of x = Ivl x x"

primrec interval_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a interval \<Rightarrow> 'b interval"
where "interval_map f (Ivl l u) = Ivl (f l) (f u)"

(* TODO: Non-emptiness should be intrinsic to the interval type,
         i.e. it should be a true subset of the set of all possible intervals.
         Is this even possible? *)
primrec nonempty :: "'a::order interval \<Rightarrow> bool"
where "nonempty (Ivl l u) = (l \<le> u)"

lemmas [simp] = lower_def upper_def

(* Definitions that make some common assumptions about lists of intervals easier to write. *)
definition all_in :: "'a::order list \<Rightarrow> 'a interval list \<Rightarrow> bool"
(infix "(all'_in)" 50)
where "x all_in I = (length x = length I \<and> (\<forall>i < length I. x!i \<in> set_of (I!i)))"

definition all_subset :: "'a::order interval list \<Rightarrow> 'a interval list \<Rightarrow> bool"
(infix "(all'_subset)" 50)
where "I all_subset J = (length I = length J \<and> (\<forall>i < length I. set_of (I!i) \<subseteq> set_of (J!i)))"

definition all_nonempty ::"'a::order interval list \<Rightarrow> bool"
where "all_nonempty I = (\<forall>i < length I. nonempty (I!i))"

lemmas [simp] = all_in_def all_subset_def all_nonempty_def

lemma mid_in_interval:
assumes "nonempty i"
shows "mid i \<in> set_of i"
proof-
  obtain l u where i_def: "i = Ivl l u" using interval.exhaust by auto
  from assms have "l \<le> u" by (simp add: i_def)
  
  {
    have "real l * Float 1 1  \<le> (real l + real u)"
      using `l \<le> u` by (simp add: Float.compute_float_one Float.compute_float_times)
    hence "real l * (Float 1 1 * Float 1 (-1)) \<le> (real l + real u) * Float 1 (-1)"
      by simp 
    hence "real l \<le> (real l + real u) * Float 1 (- 1)"
      by (simp add: Float.compute_float_one Float.compute_float_times)
  }
  moreover
  {
    have "(real l + real u) \<le> real u * Float 1 1 "
      using `l \<le> u` by (simp add: Float.compute_float_one Float.compute_float_times)
    hence "(real l + real u) * Float 1 (-1) \<le> real u * (Float 1 1 * Float 1 (-1))"
      by simp
    hence "(real l + real u) * Float 1 (- 1) \<le> real u"
      by (simp add: Float.compute_float_one Float.compute_float_times)
  }
  ultimately show ?thesis
    by (simp add: i_def)
qed

(* Arithmetic on intervals. *)
instantiation "interval" :: (plus) plus
begin
  definition "a + b = Ivl (lower a + lower b) (upper a + upper b)"
  instance ..
end
instantiation "interval" :: (minus) minus
begin
  definition "a - b = Ivl (lower a - upper b) (upper a - lower b)"
  instance ..
end
instantiation "interval" :: (uminus) uminus
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
instantiation "interval" :: (zero) zero
begin
  definition "0 = Ivl 0 0"
  instance ..
end
instantiation "interval" :: (one) one
begin
  definition "1 = Ivl 1 1"
  instance ..
end
instantiation "interval" :: ("{inverse,order}") inverse
begin
  definition "inverse a = Ivl (min (inverse (lower a)) (inverse (upper a))) (max (inverse (lower a)) (inverse (upper a)))"
  instance ..
end
instantiation "interval" :: ("{times,one,order}") power
begin
  instance ..
end

instantiation "interval" :: (linordered_idom) comm_monoid_add
begin
  instance
  proof
    fix a b c::"'a interval"
    show "a + b + c = a + (b + c)"
      by (simp add: plus_interval_def)
  next
    fix a b::"'a interval"
    show "a + b = b + a"
      by (simp add: plus_interval_def)
  next
    fix a::"'a interval"
    obtain l u where a_decomp: "a = Ivl l u" using interval.exhaust by auto
    show "0 + a = a"
      by (simp add: a_decomp plus_interval_def zero_interval_def)
  qed
end

instantiation "interval" :: (linordered_idom) cancel_semigroup_add
begin
  instance
  proof
    fix a b c::"'a interval"
    obtain la ua where [simp]: "a = Ivl la ua" using interval.exhaust by auto
    obtain lb ub where [simp]: "b = Ivl lb ub" using interval.exhaust by auto
    obtain lc uc where [simp]: "c = Ivl lc uc" using interval.exhaust by auto
    assume "a + b = a + c"
    thus "b = c"
      by (simp add: plus_interval_def)
  next
    
    fix a b c::"'a interval"
    obtain la ua where [simp]: "a = Ivl la ua" using interval.exhaust by auto
    obtain lb ub where [simp]: "b = Ivl lb ub" using interval.exhaust by auto
    obtain lc uc where [simp]: "c = Ivl lc uc" using interval.exhaust by auto
    assume "b + a = c + a"
    thus "b = c"
      by (simp add: plus_interval_def)
  qed
end

definition centered :: "float interval \<Rightarrow> float interval"
where "centered i = i - interval_of (mid i)"

lemmas [simp] = centered_def

lemma interval_mul_commute:
fixes A :: "'a::linordered_idom interval"
shows "A * B = B * A"
by (simp add: times_interval_def min.commute min.left_commute max.commute max.left_commute mult.commute)

lemma [simp]:
fixes A :: "'a::linordered_idom interval"
shows "A * 0 = 0"
by (simp add: times_interval_def zero_interval_def)

lemma [simp]:
fixes A :: "'a::linordered_idom interval"
shows "0 * A = 0"
by (simp add: times_interval_def zero_interval_def)

lemma one_times_ivl_left[simp]:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
shows "1 * A = A"
proof-
  obtain l u where [simp]: "A = Ivl l u" using interval.exhaust by auto
  show ?thesis
    using assms
    by (auto simp: times_interval_def one_interval_def)
qed

lemma one_times_ivl_right[simp]:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
shows "A * 1 = A"
using one_times_ivl_left[OF assms, unfolded interval_mul_commute]
by simp

lemma [simp]:
fixes A :: "float interval"
shows "(real a \<in> set_of (interval_map real A)) = (a \<in> set_of A)"
proof-
  obtain l u where [simp]: "A = Ivl l u" using interval.exhaust by auto
  show ?thesis by simp
qed  

(* Non-emptiness is preserved under arithmetic. *)
lemma nonempty_add:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
shows "nonempty (A + B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def B_def plus_interval_def)
qed

lemma nonempty_sub:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
shows "nonempty (A - B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def B_def minus_interval_def)
qed

lemma nonempty_neg:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
shows "nonempty (-A)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def uminus_interval_def)
qed

(* Multiplication always returns a proper interval. *)
lemma nonempty_mul[simp]:
fixes A :: "'a::linordered_idom interval"
shows "nonempty (A * B)"
by (simp add: times_interval_def)

lemma nonempty_pow:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
shows "nonempty (A ^ n)"
using assms
by (induction n, simp_all add: one_interval_def)

lemma nonempty_subset:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "set_of A \<subseteq> set_of A'"
shows "nonempty A'"
proof-
  obtain la ua where [simp]: "A = Ivl la ua" using interval.exhaust by auto
  obtain la' ua' where [simp]: "A' = Ivl la' ua'" using interval.exhaust by auto
  from assms
  show ?thesis
    by simp
qed

lemma nonempty_nonempty_equiv:
fixes A :: "'a::linordered_idom interval"
shows "nonempty A \<longleftrightarrow> set_of A \<noteq> {}"
proof-
  obtain la ua where [simp]: "A = Ivl la ua" using interval.exhaust by auto
  from assms show ?thesis by simp
qed

(* Coercions on intervals. *)
lemmas [simp] = interval_of_def

declare [[coercion "interval_of :: float \<Rightarrow> float interval"]]
declare [[coercion "interval_of :: real \<Rightarrow> real interval"]]
declare [[coercion_map interval_map]]

(* Coercion of a "float interval" to a "real interval" is homomorph. *)
lemma interval_map_real_add[simp]:
fixes i1::"float interval"
shows "interval_map real (i1 + i2) = interval_map real i1 + interval_map real i2"
by (cases i1, cases i2, simp add: plus_interval_def)

lemma interval_map_real_sub[simp]:
fixes i1::"float interval"
shows "interval_map real (i1 - i2) = interval_map real i1 - interval_map real i2"
by (cases i1, cases i2, simp add: minus_interval_def)

lemma interval_map_real_neg[simp]:
fixes i::"float interval"
shows "interval_map real (-i) = - interval_map real i"
by (cases i, simp add: uminus_interval_def)

lemma interval_map_real_mul[simp]:
fixes i1::"float interval"
shows "interval_map real (i1 * i2) = interval_map real i1 * interval_map real i2"
by (cases i1, cases i2, simp add: times_interval_def real_of_float_max real_of_float_min)

lemma interval_map_real_pow[simp]:
fixes i::"float interval"
shows "interval_map real (i ^ n) = interval_map real i ^  n"
by (cases i, induction n, simp_all add: one_interval_def)

lemma nonempty_interval_map_real[simp]:
fixes i::"float interval"
shows "nonempty (interval_map real i) = nonempty i"
by (induction i, simp_all)

(* Operations on intervals are monotone. *)
lemma set_of_add_mono:
fixes a :: "'a::ordered_ab_group_add"
assumes "a \<in> set_of A"
assumes "b \<in> set_of B"
shows "a + b \<in> set_of (A + B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub"
    using interval.exhaust by auto
  have a_def: "a \<in> {la..ua}"
    using assms(1) by (simp add: A_def set_of_def)
  have b_def: "b \<in> {lb..ub}"
    using assms(2) by (simp add: B_def set_of_def)
  show ?thesis 
    using a_def b_def
    by (simp add: A_def B_def set_of_def plus_interval_def add_mono)
qed

lemma set_of_minus_mono:
fixes a :: "'a::ordered_ab_group_add"
assumes "a \<in> set_of A"
assumes "b \<in> set_of B"
shows "a - b \<in> set_of (A - B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub"
    using interval.exhaust by auto
  have a_def: "a \<in> {la..ua}"
    using assms(1) by (simp add: A_def set_of_def)
  have b_def: "b \<in> {lb..ub}"
    using assms(2) by (simp add: B_def set_of_def)
  
  show ?thesis 
    using a_def b_def
    by (simp add: A_def B_def minus_interval_def set_of_def diff_mono)
qed

lemma set_of_uminus_mono:
fixes a :: "'a::ordered_ab_group_add"
assumes "a \<in> set_of A"
shows "-a \<in> set_of (-A)"
proof-
  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  have a_def: "a \<in> {la..ua}"
    using assms(1) by (simp add: A_def set_of_def)
  
  show ?thesis 
    using a_def
    by (simp add: A_def uminus_interval_def set_of_def)
qed

lemma set_of_mult_mono:
fixes a :: "'a::linordered_idom"
assumes "a \<in> set_of A"
assumes "b \<in> set_of B"
shows "a * b \<in> set_of (A * B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub"
    using interval.exhaust by auto
  have a_def: "a \<in> {la..ua}"
    using assms(1) by (simp add: A_def set_of_def)
  have b_def: "b \<in> {lb..ub}"
    using assms(2) by (simp add: B_def set_of_def)
    
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
assumes "nonempty A"
assumes "nonempty B"
shows "set_of A + set_of B = set_of (A + B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub"
    using interval.exhaust by auto
  from assms
  show ?thesis
    apply(simp add: A_def B_def plus_interval_def set_plus_def)
    apply(rule)
    apply(rule)
    apply(safe)
    apply(simp_all add: add_mono)
    apply(safe)
    proof(goals)
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

lemma set_of_add_right:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A + B) \<subseteq> set_of (A' + B)"
using assms(3)
by(simp add: set_of_add_distrib[OF assms(1,2), symmetric]
             set_of_add_distrib[OF nonempty_subset[OF assms(1,3)] assms(2), symmetric] set_plus_mono2)

lemma set_of_add_left:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A + B) \<subseteq> set_of (A + B')"
using set_of_add_right[OF assms(2) assms(1) assms(3)]
by (simp add: add.commute)

lemma set_of_add_cong:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
assumes "set_of A = set_of A'"
assumes "set_of B = set_of B'"
shows "set_of (A + B) = set_of (A' + B')"
unfolding set_of_add_distrib[OF assms(1,2), symmetric] assms(3,4)
apply(subst set_of_add_distrib)
using assms(3,4) nonempty_subset[OF assms(2)] nonempty_subset[OF assms(1)]
by auto

lemma set_of_add_inc_left:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A + B) \<subseteq> set_of (A' + B)"
proof
  fix x assume x_def: "x \<in> set_of (A + B)"

  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  obtain la' ua' where A'_def: "A' = Ivl la' ua'"
    using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub"
    using interval.exhaust by auto
  
  from x_def assms
  show "x \<in> set_of (A' + B)"
    by (simp add: A_def A'_def B_def plus_interval_def)
qed

lemma set_of_add_inc_right:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty B"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A + B) \<subseteq> set_of (A + B')"
using set_of_add_inc_left[OF assms]
by (simp add: add.commute)

lemma set_of_add_inc:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
assumes "set_of A \<subseteq> set_of A'"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A + B) \<subseteq> set_of (A' + B')"
using set_of_add_inc_left[OF assms(1) assms(3)]
      set_of_add_inc_right[OF assms(2) assms(4)]
by auto

lemma set_of_neg_inc:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (-A) \<subseteq> set_of (-A')"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain la' ua' where A'_def: "A' = Ivl la' ua'" using interval.exhaust by auto
  
  from assms show ?thesis
    by (simp add: A_def A'_def uminus_interval_def)
qed

lemma set_of_sub_inc_left:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A - B) \<subseteq> set_of (A' - B)"
proof-
  have "set_of (A - B) = set_of (A + (-B))"
    by (simp add: uminus_interval_def minus_interval_def plus_interval_def)
  also have "... \<subseteq> set_of (A' + (-B))"
    using assms by (rule set_of_add_inc_left)
  also have "... = set_of (A' - B)"
    by (simp add: uminus_interval_def minus_interval_def plus_interval_def)
  finally show ?thesis .
qed

lemma set_of_sub_inc_right:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty B"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A - B) \<subseteq> set_of (A - B')"
proof-
  have "set_of (A - B) = set_of (A + (-B))"
    by (simp add: uminus_interval_def minus_interval_def plus_interval_def)
  also have "... \<subseteq> set_of (A + (-B'))"
    using assms by (simp add: set_of_add_inc_right nonempty_neg set_of_neg_inc)
  also have "... \<subseteq> set_of (A - B')"
    by (simp add: uminus_interval_def minus_interval_def plus_interval_def)
  finally show ?thesis .
qed

lemma set_of_sub_inc:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
assumes "set_of A \<subseteq> set_of A'"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A - B) \<subseteq> set_of (A' - B')"
using set_of_sub_inc_left[OF assms(1) assms(3)]
      set_of_sub_inc_right[OF assms(2) assms(4)]
by auto

lemma set_of_distrib_right:
fixes A1 :: "'a::linordered_idom interval"
shows "set_of ((A1 + A2) * B) \<subseteq> set_of (A1 * B + A2 * B)"
proof
  fix x assume assm: "x \<in> set_of ((A1 + A2) * B)"
  
  obtain la1 ua1 where A1_def: "A1 = Ivl la1 ua1" using interval.exhaust by auto
  obtain la2 ua2 where A2_def: "A2 = Ivl la2 ua2" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  
  from assm
  have a1: "min (min ((la1 + la2) * lb) ((ua1 + ua2) * lb)) (min ((la1 + la2) * ub) ((ua1 + ua2) * ub)) \<le> x"
  and  a2: "x \<le> max (max ((la1 + la2) * lb) ((ua1 + ua2) * lb)) (max ((la1 + la2) * ub) ((ua1 + ua2) * ub))"
    by (auto simp: A1_def A2_def B_def times_interval_def plus_interval_def)
    
  show "x \<in> set_of (A1 * B + A2 * B)"
    apply(simp add: A1_def A2_def B_def times_interval_def plus_interval_def)
    apply(rule conjI[OF order.trans[OF _ a1]  order.trans[OF a2]])
    apply (smt add_mono distrib_right dual_order.trans min.cobounded1 min_def)
    apply (smt add_mono distrib_right dual_order.trans max.cobounded2 max_def)
    done
qed

(* TODO: Clean up this proof. Does this really only hold for fields? *)
lemma set_of_mult_distrib:
fixes A :: "'a::linordered_field interval"
assumes "nonempty A"
assumes "nonempty B"
shows "set_of (A * B) = set_of A * set_of B"
proof-
  obtain la ua where A_def[simp]: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def[simp]: "B = Ivl lb ub" using interval.exhaust by auto
  
  have min_dist_right_pos[simp]: "\<And>a b c::'a. 0 \<le> c \<Longrightarrow> min (a * c) (b * c) = min a b * c"
    by (metis le_less min_def mult.commute mult_le_cancel_right mult_right_mono mult_zero_left)
  have min_dist_right_neg[simp]: "\<And>a b c::'a. c < 0 \<Longrightarrow> min (a * c) (b * c) = max a b * c"
    by (simp add: max_def min_def)
  have max_dist_right_pos[simp]: "\<And>a b c::'a. 0 \<le> c \<Longrightarrow> max (a * c) (b * c) = max a b * c"
    by (metis max.absorb_iff1 max_def mult_right_mono)
  have max_dist_right_neg[simp]: "\<And>a b c::'a. c < 0 \<Longrightarrow> max (a * c) (b * c) = min a b * c"
    by (simp add: max_def min_def)
  have min_dist_left_pos[simp]: "\<And>a b c::'a. 0 \<le> c \<Longrightarrow> min (c * a) (c * b) = c * min a b"
    by (metis le_less min_def mult.commute mult_le_cancel_right mult_right_mono mult_zero_left)
  have min_dist_left_neg[simp]: "\<And>a b c::'a. c < 0 \<Longrightarrow> min (c * a) (c * b) = c * max a b "
    by (simp add: max_def min_def)
  have max_dist_left_pos[simp]: "\<And>a b c::'a. 0 \<le> c \<Longrightarrow> max (c * a) (c * b) = c * max a b"
    by (metis max.absorb_iff1 max_def mult_left_mono)
  have max_dist_left_neg[simp]: "\<And>a b c::'a. c < 0 \<Longrightarrow> max (c * a) (c * b) = c * min a b"
    by (simp add: max_def min_def)
  
  have "la \<le> ua" "lb \<le> ub" using assms by auto
  hence min_la_ua[simp]: "min la ua = la"
  and   max_la_ua[simp]: "max la ua = ua"
  and   min_la_ua[simp]: "min lb ub = lb"
  and   max_la_ua[simp]: "max lb ub = ub" by auto
  
  let ?C="set_of (A * B) = {la*lb..ua*ub} \<or> set_of (A * B) = {ua*lb..la*lb} \<or>
          set_of (A * B) = {ua*lb..la*ub} \<or> set_of (A * B) = {ua*lb..ua*ub} \<or>
          set_of (A * B) = {la*ub..la*lb} \<or> set_of (A * B) = {la*ub..ua*lb} \<or>
          set_of (A * B) = {la*ub..ua*ub} \<or> set_of (A * B) = {ua*ub..la*lb}"
  {
    assume "0 \<le> la" "0 \<le> ua" "0 \<le> lb" "0 \<le> ub"
    hence "set_of (A * B) = {la*lb..ua*ub}"
      using `la \<le> ua` `lb \<le> ub`
      by (simp add: times_interval_def)
    hence ?C by linarith
  } moreover {
    assume "0 \<le> la" "0 \<le> ua" "lb < 0" "0 \<le> ub"
    hence "set_of (A * B) = {ua*lb..la*lb} \<or> set_of (A * B) = {ua*lb..ua*ub} \<or> set_of (A * B) = {la*ub..la*lb} \<or> set_of (A * B) = {la*ub..ua*ub}"
      by (simp add: times_interval_def, simp add: max_def min_def)
    hence ?C by linarith
  } moreover {
    assume "0 \<le> la" "0 \<le> ua" "lb < 0" "ub < 0"
    hence "set_of (A * B) = {ua*lb..la*ub}" by (simp add: times_interval_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "0 \<le> ua" "0 \<le> lb" "0 \<le> ub"
    hence "set_of (A * B) = {la*ub..ua*ub}" by (simp add: times_interval_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "0 \<le> ua" "lb < 0" "0 \<le> ub"
    hence "set_of (A * B) = {ua*lb..la*lb} \<or> set_of (A * B) = {ua*lb..ua*ub} \<or> set_of (A * B) = {la*ub..la*lb} \<or> set_of (A * B) = {la*ub..ua*ub} \<or> set_of (A * B) = {ua*ub..la*lb}"
      by (simp add: times_interval_def min_def max_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "0 \<le> ua" "lb < 0" "ub < 0"
    hence "set_of (A * B) = {ua*lb..la*lb}" by (simp add: times_interval_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "ua < 0" "0 \<le> lb" "0 \<le> ub"
    hence "set_of (A * B) = {la*ub..ua*lb}" by (simp add: times_interval_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "ua < 0" "lb < 0" "0 \<le> ub"
    hence "set_of (A * B) = {ua*lb..la*lb} \<or> set_of (A * B) = {ua*lb..ua*ub} \<or>
           set_of (A * B) = {la*ub..la*lb} \<or> set_of (A * B) = {la*ub..ua*ub} \<or>
           set_of (A * B) = {ua*ub..la*lb}" using `la \<le> ua`
      by (simp add: times_interval_def min_def max_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "ua < 0" "lb < 0" "ub < 0"
    hence "set_of (A * B) = {ua*ub..la*lb}" by (simp add: times_interval_def)
    hence ?C by linarith
  } moreover {
    assume "la < 0" "ua < 0" "0 \<le> lb" "ub < 0"
    hence ?C using `lb \<le> ub` by simp
  } moreover {
    assume "0 \<le> la" "ua < 0" "0 \<le> lb" "0 \<le> ub"
    hence ?C using `la \<le> ua` by simp
  } moreover {
    assume "0 \<le> la" "0 \<le> ua" "0 \<le> lb" "ub < 0"
    hence ?C using `lb \<le> ub` by simp
  } moreover {
    assume "0 \<le> la" "ua < 0" "0 \<le> lb" "ub < 0"
    hence ?C using `lb \<le> ub` by simp
  } moreover {
    assume "0 \<le> la" "ua < 0" "lb < 0" "0 \<le> ub"
    hence ?C using `la \<le> ua` by simp
  } moreover {
    assume "0 \<le> la" "ua < 0" "lb < 0" "ub < 0"
    hence ?C using `la \<le> ua` by simp
  } moreover {
    assume "la < 0" "0 \<le> ua" "0 \<le> lb" "ub < 0"
    hence ?C using `lb \<le> ub` by simp
  } ultimately have ?C
    unfolding not_le[symmetric]
    by metis
  
  {
    fix x assume "x \<in> set_of A * set_of B"
    from set_times_elim[OF this] obtain a b where x_decomp: "x = a * b" "a \<in> set_of A" "b \<in> set_of B"
      by auto
      
    from x_decomp(2,3) have "x \<in> set_of (A * B)"
      apply(simp add: times_interval_def x_decomp(1))
      apply(cases "0 \<le> lb", simp)
      apply(cases "0 \<le> ub", simp)
      apply(cases "0 \<le> la", simp)
      apply(safe)[1]
      apply(simp_all add: mult_mono)[2]
      apply(cases "0 \<le> ua", simp)
      apply(safe)[1]
      apply(smt le_less max_def max_dist_left_neg max_dist_right_pos min_def not_le order.trans)
      apply(simp add: mult_mono)
      apply(simp)
      apply(safe)[1]
      apply(smt dual_order.trans linear max_def min.assoc min_def min_dist_right_neg min_dist_right_pos mult.commute mult_le_0_iff not_le zero_le_mult_iff)
      apply(smt le_less max_def max_dist_left_pos max_dist_right_neg min_def mult.commute not_le order.trans)
      apply(simp)
      apply(simp)
      apply(cases "0 \<le> ub", simp)
      apply(cases "0 \<le> la")
      apply(simp add: min_def)
      apply(safe)[1]
      apply(smt linear max_def min_def min_dist_left_pos min_dist_right_neg not_less order.trans)
      apply(smt max.coboundedI2 mult.commute mult_mono order_trans)
      apply(metis (mono_tags, lifting) dual_order.trans linear mult_le_0_iff zero_le_mult_iff)
      apply(simp add: max_def)
      apply(smt mult.commute mult_mono order_trans)
      apply(cases "0 \<le> ua")
      apply(safe)[1]
      apply(simp add: min_def)
      apply(smt le_less max_def min_def min_dist_left_pos min_dist_right_neg min_le_iff_disj mult.commute mult_le_0_iff)
      apply(simp add: max_def)
      apply(smt linear max.left_commute max_def min_dist_right_neg min_le_iff_disj mult.commute mult_mono not_le)
      apply(safe)[1]
      apply(simp add: min_def)
      apply(safe)[1]
      apply(metis dual_order.trans linear mult_le_0_iff)
      apply(smt linear mult_minus_left mult_mono neg_le_iff_le order_trans zero_le_mult_iff)
      apply(simp add: max_def)
      apply(safe)[1]
      apply(metis dual_order.trans linear mult_le_0_iff)
      apply(smt eq_iff max.coboundedI2 max.orderE max_dist_right_neg min_def mult.commute not_less)
      apply(simp)
      apply(cases "0 \<le> ua", simp)
      apply(cases "0 \<le> la", simp)
      apply(safe)[1]
      apply(smt eq_iff le_less max.coboundedI2 max.orderE min.assoc min.commute min_def min_dist_left_pos min_dist_right_neg)
      apply(smt dual_order.trans leD leI max_dist_left_neg max_less_iff_conj min_absorb2 mult.commute mult_left_mono)
      apply(simp)
      apply(safe)[1]
      apply(smt leD leI max_def max_dist_left_neg max_less_iff_conj min_absorb2 mult.commute mult_left_mono)
      apply(smt eq_refl max.left_commute max_def max_dist_left_neg max_dist_right_neg max_less_iff_conj min.orderE not_leE)
      apply(simp)
      by (smt eq_iff leI max.orderE max_less_iff_conj min_dist_right_neg min_le_iff_disj mult.commute)
  }
  moreover
  {
    have mult_inverse: "\<And>x a b c::'a. a * c \<le> x \<Longrightarrow> x \<le> b * c \<Longrightarrow> \<exists>d. x = d * c \<and> (d \<in> {a..b} \<or> d \<in> {b..a})"
    proof(goals)
      case (1 x a b c)
      {
        assume "c = 0"
        hence "?case" using 1 by auto
      } moreover {
        assume "0 < c"
        hence "a \<le> x / c" "x / c \<le> b" "x = (x/c) * c"
          using 1 by (auto simp: pos_le_divide_eq pos_divide_le_eq)
        hence "?case" by fastforce
      } moreover {
        assume "c < 0"
        hence "x / c \<le> a" "b \<le> x / c" "x = (x/c) * c"
          using 1 by (auto simp: neg_le_divide_eq neg_divide_le_eq)
        hence "?case" by fastforce
      } ultimately show ?case by fastforce
    qed
    
    fix x assume "x \<in> set_of (A * B)"
    hence"x \<in> set_of A * set_of B"
      using `?C`
      apply(simp add: times_interval_def set_times_def)
      apply(safe)
      proof(goals)
        case 1 {
          assume x_le: "x \<le> ua * lb"
          have le_x: "la * lb \<le> x" using 1(1,3) by simp
          from mult_inverse[OF le_x x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by fastforce
        } moreover {
          assume less_x: "ua * lb < x"
          have x_le: "x \<le> ub*ua" using 1(2,4) by (simp add: mult.commute)
          from mult_inverse[OF  less_imp_le[OF less_x, unfolded mult.commute] x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by (subst mult.commute, fastforce)
        } ultimately show ?case by linarith
      next
        case 2
        hence "ua * lb \<le> x" "x \<le> la * lb" by auto
        from mult_inverse[OF this] `la \<le> ua` `lb \<le> ub`
        show ?case by fastforce
      next
        case 3 {
          assume x_le: "x \<le> ub * ua"
          have le_x: "lb * ua \<le> x" using 3(1,3) by (simp add: mult.commute)
          from mult_inverse[OF le_x x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by (subst mult.commute, fastforce)
        } moreover {
          assume less_x: "ub * ua < x"
          have x_le: "x \<le> la * ub" using 3(2,4) by (simp add: mult.commute)
          from mult_inverse[OF  less_imp_le[OF less_x, unfolded mult.commute] x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by fastforce
        } ultimately show ?case by linarith
      next
        case 4
        hence "lb * ua \<le> x" "x \<le> ub * ua" by (auto simp: mult.commute)
        from mult_inverse[OF this] `la \<le> ua` `lb \<le> ub`
        show ?case by (subst mult.commute, fastforce)
      next
        case 5
        hence "ub * la \<le> x" "x \<le> lb * la" by (auto simp: mult.commute)
        from mult_inverse[OF this] `la \<le> ua` `lb \<le> ub`
        show ?case by (subst mult.commute, fastforce)
      next
        case 6 {
          assume x_le: "x \<le> ua * ub"
          have le_x: "la * ub \<le> x" using 6(1,3) by simp
          from mult_inverse[OF le_x x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by fastforce
        } moreover {
          assume "ua * ub < x" hence le_x: "ub * ua \<le> x" by (simp add: mult.commute)
          have x_le: "x \<le> lb * ua" using 6(2,4) by (simp add: mult.commute)
          from mult_inverse[OF le_x x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by (subst mult.commute, fastforce)
        } ultimately show ?case by linarith
      next
        case 7
        hence "la * ub \<le> x" "x \<le> ua * ub" by auto
        from mult_inverse[OF this] `la \<le> ua` `lb \<le> ub`
        show ?case by fastforce
      next
        case 8 {
          assume x_le: "x \<le> la * ub"
          have le_x: "ua * ub \<le> x" using 8(1,3) by simp
          from mult_inverse[OF le_x x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by fastforce
        } moreover {
          assume "la * ub < x" hence le_x: "ub * la \<le> x" by (simp add: mult.commute)
          have x_le: "x \<le> lb * la" using 8(2,4) by (simp add: mult.commute)
          from mult_inverse[OF le_x x_le] `la \<le> ua` `lb \<le> ub`
          have ?case by (subst mult.commute, fastforce)
        } ultimately show ?case by linarith
      qed
  }
  ultimately show ?thesis
    by auto
qed

lemma set_of_mul_inc_left:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A * B) \<subseteq> set_of (A' * B)"
proof
  fix x assume x_def: "x \<in> set_of (A * B)"

  obtain la ua where A_def: "A = Ivl la ua"
    using interval.exhaust by auto
  obtain la' ua' where A'_def: "A' = Ivl la' ua'"
    using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub"
    using interval.exhaust by auto
  
  from x_def assms
  show "x \<in> set_of (A' * B)"
    apply(simp add: A_def A'_def B_def times_interval_def)
    apply(safe)
    apply(smt min.absorb_iff2 min.coboundedI2 min_def mult_le_cancel_right)
    by (smt eq_iff le_max_iff_disj max_def mult_le_cancel_right)
qed

lemma set_of_mul_inc_right:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty B"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A * B) \<subseteq> set_of (A * B')"
unfolding interval_mul_commute[of A]
by (rule set_of_mul_inc_left[OF assms])

lemma set_of_mul_inc:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "nonempty B"
assumes "set_of A \<subseteq> set_of A'"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A * B) \<subseteq> set_of (A' * B')" 
using set_of_mul_inc_right[OF assms(2,4)] set_of_mul_inc_left[OF assms(1,3)]
by auto

lemma set_of_pow_inc:
fixes A :: "'a::linordered_idom interval"
assumes "nonempty A"
assumes "set_of A \<subseteq> set_of A'"
shows "set_of (A^n) \<subseteq> set_of (A'^n)"
using assms
by (induction n, simp_all add: nonempty_pow set_of_mul_inc)

lemma set_of_distrib_left:
fixes A1 :: "'a::linordered_idom interval"
shows "set_of (B * (A1 + A2)) \<subseteq> set_of (B * A1 + B * A2)"
unfolding interval_mul_commute
by (rule set_of_distrib_right[unfolded interval_mul_commute])

lemma set_of_distrib_right_left:
fixes A1 :: "'a::linordered_idom interval"
assumes "nonempty A1"
assumes "nonempty A2"
assumes "nonempty B1"
assumes "nonempty B2"
shows "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * B1 + A1 * B2 + A2 * B1 + A2 * B2)"
proof-
  have "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * (B1 + B2) + A2 * (B1 + B2))"
    by (rule set_of_distrib_right)
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + A2 * (B1 + B2))"
    apply(rule set_of_add_inc_left)
    apply(simp add: assms(1) assms(3) assms(4) nonempty_add)
    by (rule set_of_distrib_left)
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + (A2 * B1 + A2 * B2))"
    apply(rule set_of_add_inc_right)
    apply(simp add: assms(2) assms(3) assms(4) nonempty_add)
    by (rule set_of_distrib_left)
  finally show ?thesis
    by (simp add: add.assoc)
qed

lemma set_of_mul_contains_zero:
fixes A :: "'a::linordered_idom interval"
assumes "0 \<in> set_of A \<or> 0 \<in> set_of B"
shows "0 \<in> set_of (A * B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  from assms show ?thesis
    apply(simp add: A_def B_def times_interval_def)
    by (metis (full_types) le_max_iff_disj linear min.coboundedI1 min.coboundedI2 mult_le_0_iff mult_nonneg_nonneg mult_nonpos_nonpos)
qed

end