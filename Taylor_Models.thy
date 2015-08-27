theory Taylor_Models
imports "Generic_Multivariate_Polynomials"
        "~~/src/HOL/Decision_Procs/Approximation"
        "~~/src/HOL/Library/Function_Algebras"
        "~~/src/HOL/Library/Set_Algebras"
begin

(* I define my own interval type here. This is so that I can write polynomials with interval coefficients. *)
datatype 'a interval = Ivl 'a 'a

primrec lower :: "'a interval \<Rightarrow> 'a"
where "lower (Ivl l u) = l"

primrec upper :: "'a interval \<Rightarrow> 'a"
where "upper (Ivl l u) = u"

primrec set_of :: "('a::ord) interval \<Rightarrow> 'a set"
where "set_of (Ivl l u) = {l..u}"

primrec prod_of :: "('a::ord) interval \<Rightarrow> 'a \<times> 'a"
where "prod_of (Ivl l u) = (l, u)"

(* TODO: Validity should be intrinsic to the interval type. *)
primrec valid_ivl :: "('a::ord) interval \<Rightarrow> bool"
where "valid_ivl (Ivl l u) = (l \<le> u)"

lemmas [simp] = lower_def upper_def

(* Type instantiations for intervals. This allows us to write and evaluate interval polynomials. *)
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
instantiation "interval" :: ("{times, ord}") times
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
instantiation "interval" :: ("{inverse,ord}") inverse
begin
  definition "inverse a = Ivl (min (inverse (lower a)) (inverse (upper a))) (max (inverse (lower a)) (inverse (upper a)))"
  instance ..
end
instantiation "interval" :: ("{times,one,ord}") power
begin
  instance ..
end

value "Ivl (0::real) 1 * Ivl 0 1"
value "Ivl (-1::real) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 + Ivl 0 1"

lemmas [simp] = zero_interval_def one_interval_def

(* Interval arithmetic is commutative. *)
lemma interval_add_commute:
fixes A :: "'a::linordered_idom interval"
shows "A + B = B + A"
using interval.exhaust
by (auto simp: plus_interval_def)

lemma interval_mul_commute:
fixes A :: "'a::linordered_idom interval"
shows "A * B = B * A"
using interval.exhaust
by (auto simp: times_interval_def min.commute min.left_commute max.commute max.left_commute mult.commute)

(* Interval arithmetic is associative. *)
lemma interval_add_assoc:
fixes A :: "'a::linordered_idom interval"
shows "(A + B) + D = A + (B + D)"
using interval.exhaust
by (auto simp: plus_interval_def)

(* Validity is preserved under arithmetic. *)
lemma valid_ivl_add:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
assumes "valid_ivl B"
shows "valid_ivl (A + B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def B_def plus_interval_def)
qed

lemma valid_ivl_sub:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
assumes "valid_ivl B"
shows "valid_ivl (A - B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def B_def minus_interval_def)
qed

lemma valid_ivl_neg:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
shows "valid_ivl (-A)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def uminus_interval_def)
qed

lemma valid_ivl_mul:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
assumes "valid_ivl B"
shows "valid_ivl (A * B)"
proof-
  obtain la ua where A_def: "A = Ivl la ua" using interval.exhaust by auto
  obtain lb ub where B_def: "B = Ivl lb ub" using interval.exhaust by auto
  from assms show ?thesis by (simp add: A_def B_def times_interval_def)
qed

lemma valid_ivl_pow:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
shows "valid_ivl (A ^ n)"
using assms
by (induction n, simp_all add: valid_ivl_mul)

(* Polynomial with interval coefficients. *)
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 (-6))] (poly.Add (poly.C (Ivl (Float 3 (-5)) (Float 3 (-5)))) (poly.Bound 0))"

(* TODO: - For now, I hard-code the precision, because I don't want to carry it around.
           Later, it will become explicit. *)
fun compute_bound :: "floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
where "compute_bound p I = (case approx 64 p (map (\<lambda>i. case i of Ivl a b \<Rightarrow> Some (a, b)) I) of Some (a, b) \<Rightarrow> Some (Ivl a b) | _ \<Rightarrow> None)"

value "compute_bound (Add (Var 0) (Num 3)) [Ivl 1 2]"

lemma compute_bound_correct:
assumes "Some (Ivl l u) = compute_bound f I"
assumes "\<And>n. n < length I \<Longrightarrow> i!n \<in> set_of (I!n)"
assumes "length I = length i"
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
        using `n < length I` by (auto simp: I_def set_of_def)
      moreover have "map real i ! n = real (i ! n)"
        apply(rule List.nth_map)
        using `n < length I` `length I = length i`
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
    
(* Conversions on intervals. *)
definition interval_of :: "'a \<Rightarrow> 'a interval"
where "interval_of x = Ivl x x"

primrec interval_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a interval \<Rightarrow> 'b interval"
where "interval_map f (Ivl l u) = Ivl (f l) (f u)"

lemmas [simp] = interval_of_def

declare [[coercion "interval_of :: float \<Rightarrow> float interval"]]
declare [[coercion "interval_of :: real \<Rightarrow> real interval"]]
declare [[coercion_map interval_map]]
declare [[coercion_map poly_map]]

(* Apply float interval arguments to a float poly. *)
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 6)] (poly.Add (poly.C (Float 3 5)) (poly.Bound 0))"

(* Coercion of a "float interval" to a "real interval" is homomorph. *)
lemma interval_map_real_add:
fixes i1::"float interval"
shows "interval_map real (i1 + i2) = interval_map real i1 + interval_map real i2"
by (cases i1, cases i2, simp add: plus_interval_def)

lemma interval_map_real_sub:
fixes i1::"float interval"
shows "interval_map real (i1 - i2) = interval_map real i1 - interval_map real i2"
by (cases i1, cases i2, simp add: minus_interval_def)

lemma interval_map_real_neg:
fixes i::"float interval"
shows "interval_map real (-i) = - interval_map real i"
by (cases i, simp add: uminus_interval_def)

lemma interval_map_real_mul:
fixes i1::"float interval"
shows "interval_map real (i1 * i2) = interval_map real i1 * interval_map real i2"
by (cases i1, cases i2, simp add: times_interval_def real_of_float_max real_of_float_min)

lemma interval_map_real_pow:
fixes i::"float interval"
shows "interval_map real (i ^ n) = interval_map real i ^  n"
by (cases i, induction n, simp_all add: interval_map_real_mul)

lemma valid_ivl_interval_map_real[simp]:
fixes i::"float interval"
shows "valid_ivl (interval_map real i) = valid_ivl i"
by (induction i, simp_all)

(* Coercing a "float poly" into a "real poly" does not change the structure of the polynomial. *)
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
using assms
by (induction p, simp_all add: interval_map_real_add interval_map_real_sub interval_map_real_neg interval_map_real_mul interval_map_real_pow)

(* TODO: This lemma is a mess and similar to Ipoly_real_float_interval_eqiv. *)
lemma Ipoly_real_float_interval_eqiv':
fixes p::"float poly" and xs::"float interval list"
assumes "num_params p \<le> length xs"
shows "Ipoly (map (interval_map real) xs) (poly_map interval_of (poly_map real p)) = interval_map real (Ipoly xs (poly_map interval_of p))"
using assms
by (induction p, simp_all add: interval_map_real_add interval_map_real_sub interval_map_real_neg interval_map_real_mul interval_map_real_pow)

lemma valid_ivl_Ipoly:
fixes A :: "'a::linordered_idom interval list"
fixes p :: "'a poly"
assumes "num_params p \<le> length I"
assumes "\<And>n. n < length I \<Longrightarrow> valid_ivl (I!n)"
shows "valid_ivl (Ipoly I (poly_map interval_of p))"
using assms
by (induction p, simp_all add: valid_ivl_add valid_ivl_sub valid_ivl_mul valid_ivl_neg valid_ivl_pow)

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

(* TODO: Clean this proof up! *)
lemma set_of_add_distrib:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
assumes "valid_ivl B"
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
by (induction n, simp_all add: set_of_mult_mono)

lemma set_of_inc_sum_left:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl A"
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

lemma set_of_inc_sum_right:
fixes A :: "'a::linordered_idom interval"
assumes "valid_ivl B"
assumes "set_of B \<subseteq> set_of B'"
shows "set_of (A + B) \<subseteq> set_of (A + B')"
using set_of_inc_sum_left[OF assms]
by (simp add: interval_add_commute)

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

lemma set_of_distrib_left:
fixes A1 :: "'a::linordered_idom interval"
shows "set_of (B * (A1 + A2)) \<subseteq> set_of (B * A1 + B * A2)"
unfolding interval_mul_commute
by (rule set_of_distrib_right[unfolded interval_mul_commute])

lemma set_of_distrib_right_left:
fixes A1 :: "'a::linordered_idom interval"
assumes "valid_ivl A1"
assumes "valid_ivl A2"
assumes "valid_ivl B1"
assumes "valid_ivl B2"
shows "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * B1 + A1 * B2 + A2 * B1 + A2 * B2)"
proof-
  have "set_of ((A1 + A2) * (B1 + B2)) \<subseteq> set_of (A1 * (B1 + B2) + A2 * (B1 + B2))"
    by (rule set_of_distrib_right)
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + A2 * (B1 + B2))"
    apply(rule set_of_inc_sum_left)
    apply(simp add: assms(1) assms(3) assms(4) valid_ivl_add valid_ivl_mul)
    by (rule set_of_distrib_left)
  also have "... \<subseteq> set_of ((A1 * B1 + A1 * B2) + (A2 * B1 + A2 * B2))"
    apply(rule set_of_inc_sum_right)
    apply(simp add: assms(2) assms(3) assms(4) valid_ivl_add valid_ivl_mul)
    by (rule set_of_distrib_left)
  finally show ?thesis
    by (simp add: interval_add_assoc)
 qed
    

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
assumes "\<And>n. n < length I \<Longrightarrow> x!n \<in> set_of (I!n)"
assumes "length x = length I"
assumes "valid_tm I f t"
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
    apply(induction p, simp_all)
    by (simp add: interval_map_real_add)
qed

(* Operations on taylor models. *)
fun TMNeg :: "taylor_model \<Rightarrow> taylor_model"
where "TMNeg (TaylorModel p i) = TaylorModel (poly.Neg p) (-i)"

fun TMAdd :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMAdd (TaylorModel p1 i1) (TaylorModel p2 i2) = TaylorModel (poly.Add p1 p2) (i1+i2)"

fun TMSub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
where "TMSub t1 t2 = TMAdd t1 (TMNeg t2)"

(* Multiplicate taylor models by multiplicating their polynomials and increasing the error. 
   TODO: Currently, this increases the degree of the polynomial! *)
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
        by (simp_all add: interval_map_real_mul set_of_mult_mono)
      also have "... = set_of (interval_map real (i1 * Ipoly I (poly_map interval_of p2) + Ipoly I (poly_map interval_of p1) * i2 + i1 * i2))"
        by (simp add: v1 v2 t1_def(2) t2_def(2) interval_map_real_add set_of_add_distrib valid_ivl_add valid_ivl_mul)
      finally have "(f * g) x - Ipoly x p1 * Ipoly x p2  \<in> set_of (interval_map real (i1 * Ipoly I (poly_map interval_of p2) + Ipoly I (poly_map interval_of p1) * i2 + i1 * i2))"
        .

      thus ?case
      by simp
    next
      case 2
      show ?case
        using t1_def(2) t2_def(2) v1 v2
        by (simp add: valid_ivl_add valid_ivl_mul)
    qed
qed

(* Compute taylor models of degree n from floatarith expressions. *)
fun compute_taylor_model :: "nat \<Rightarrow> real interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
where "compute_taylor_model _ I (Num c) = Some (TaylorModel (poly.C c) (Ivl 0 0))"
    | "compute_taylor_model _ I (Var n) = Some (TaylorModel (poly.Bound n) (Ivl 0 0))"
    | "compute_taylor_model n I (Add a b) = (
         case (compute_taylor_model n I a, compute_taylor_model n I b) 
         of (Some t1, Some t2) \<Rightarrow> Some (TMAdd t1 t2) | _ \<Rightarrow> None)"
    | "compute_taylor_model n I (Minus a) = (
         case compute_taylor_model n I a of Some t1 \<Rightarrow> Some (TMNeg t1) | _ \<Rightarrow> None)"
    | "compute_taylor_model n I _ = None"

lemma compute_taylor_params_bound:
assumes "num_vars f \<le> length I"
assumes "Some t = compute_taylor_model n I f "
shows "num_params (poly_tm t) \<le> length I"
using assms
apply(induction f arbitrary: t)
proof(goals)
case (Add a b t)
  obtain t1 where compute_a: "Some t1 = compute_taylor_model n I a"
    by (metis (no_types, lifting) Add(4) compute_taylor_model.simps(3) option.case_eq_if option.collapse prod.case)
  then obtain p1 i1 where t1_def: "t1 = TaylorModel p1 i1"
      using taylor_model.exhaust by auto
  obtain t2 where compute_b: "Some t2 = compute_taylor_model n I b"
    by (smt Add(4) compute_taylor_model.simps(3) option.case_eq_if option.collapse prod.case)
  then obtain p2 i2 where t2_def: "t2 = TaylorModel p2 i2"
      using taylor_model.exhaust by auto
  have t_def: "t = TMAdd t1 t2"
    using Add(4) compute_a compute_b
    by (metis compute_taylor_model.simps(3) option.case(2) option.inject prod.case)
    
  from Add(3)
  have "num_vars a \<le> length I"
       "num_vars b \<le> length I"
    by auto
  note num_params = Add(1)[OF this(1) compute_a, unfolded t1_def, simplified] 
                    Add(2)[OF this(2) compute_b, unfolded t2_def, simplified]
  
  show ?case
    using num_params
    by (simp add: t_def t1_def t2_def)
next
case (Minus a t)
  obtain t' where compute_a: "Some t' = compute_taylor_model n I a"
    by (metis Minus.prems(2) compute_taylor_model.simps(4) option.case_eq_if option.collapse)
  then obtain p' i' where t'_def: "t' = TaylorModel p' i'"
      using taylor_model.exhaust by auto
  have t_def: "t = TMNeg t'"
    using Minus.prems(2) compute_a
    by (simp, metis option.inject option.simps(5))
    
  from Minus.prems(1)
  have "num_vars a \<le> length I"
    by auto
  from Minus(1)[OF this(1) compute_a, unfolded t'_def, simplified]
  show ?case
    by (simp add: t_def t'_def)
qed simp_all

lemma
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
qed (simp_all add: valid_tm_def compute_taylor_params_bound)


end