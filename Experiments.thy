theory Experiments
imports Taylor_Models
begin

(* Trying out arithmetic on intervals and polynomials with interval coefficients. *)
value "Ivl (-1::float) 1 + Ivl 0 1"
value "Ivl (-8::float) 2 + Ivl (-2) (-1)"
value "Ivl (0::real) 1 * Ivl 0 1"
value "Ivl (-10::real) 6 * Ivl (-4) 2"
value "Ivl (-1::real) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 * Ivl 0 1"
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 (-6))] (poly.Add (poly.C (Ivl (Float 3 (-5)) (Float 3 (-5)))) (poly.Bound 0))"

value "compute_bound_fa 64 (Add (Var 0) (Num 3)) [Ivl 1 2]"

value "map_option (interval_map real_of_float) (compute_bound_fa 16 (Cos (Var 0)) [Ivl (-1) 1])"

value "map (interval_map real_of_float) (the (tmf_ivl_poly 32 10 (Ivl 0 2) 1 (Cos (Var 0))))"

(* Compute some taylor models. *)
value "the (compute_tm 32 7 [Ivl 0 2] [1] (Num 2))"
value "the (compute_tm 32 7 [Ivl 0 2] [1] (Var 0))"
value "the (compute_tm 32 7 [Ivl 0 2, Ivl 0 2] [1,1] (Add (Var 0) (Var 1)))"
value "tm_norm_poly (the (compute_tm 32 10 [Ivl (-1) 1] [0] (Cos (Var 0))))"
value [code] "tm_norm_poly (the (compute_tm 32 7 [Ivl (-1) 1, Ivl (-1) 1] [0, 0] (Add (Exp (Add (Var 0) (Var 1))) (Cos (Mult (Var 0) (Var 1))))))"

value "real_of_rat (Fract 10 3) "


(* Some performance tests. *)
definition "test_expr = (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2))"

definition "n = 5"
definition "prec = 32"

definition "test_naive (u::unit) = compute_ivl_bound_naive prec n test_expr [Ivl 0 10]"
definition "test_best (u::unit) = compute_ivl_bound_subdiv prec 5 n test_expr [Ivl 0 10]"

ML \<open>val test_best = @{code test_best}\<close>
ML \<open>val test_naive = @{code test_best}\<close>

value "test_best ()"
value "test_naive ()"

ML \<open>Timing.timeit test_best\<close>
ML \<open>Timing.timeit test_naive\<close>

(*definition "approx_cos I = (case the (compute_tm 32 10 I (map mid I) (Cos (Var 0))) of TaylorModel p e \<Rightarrow> (p, e))"

fun approx_cos_error
where "approx_cos_error I = snd (approx_cos [Ivl (-1) 1])"

fun approx_cos_naive
where "approx_cos_naive I = Ipoly I (polynate (polysubst0 (poly.Sub (poly.Bound 0) (poly.C (mid (hd I)))) (fst (approx_cos I))))"

fun approx_cos_trans
where "approx_cos_trans I = Ipoly (list_op op- I (map mid I)) (fst (approx_cos I))"

fun approx_cos_best
where "approx_cos_best I = compute_bound_poly (fst (approx_cos I)) I (map mid I)"

value "approx_cos_error [Ivl (-1) 1]"
value "approx_cos_error [Ivl 1 3]"
value "approx_cos_error [Ivl 3 5]"
value "approx_cos_error [Ivl 5 7]"
value "approx_cos_error [Ivl 7 9]"
value "approx_cos_error [Ivl 9 11]"

value "approx_cos_naive [Ivl (-1) 1]"
value "approx_cos_naive [Ivl 1 3]"
value "approx_cos_naive [Ivl 3 5]"
value "approx_cos_naive [Ivl 5 7]"
value "approx_cos_naive [Ivl 7 9]"
value "approx_cos_naive [Ivl 9 11]"

(*
Direct evaluation of the approximation polynomial:
cos(09.00): -0.9111303674289957
cos(09.25): -0.9847651789784349
cos(09.50): -0.9971721560252718
cos(09.75): -0.9475798037387368
cos(10.00): -0.8390715288696811
cos(10.25): -0.6783938503053173
cos(10.50): -0.4755369279566821
cos(10.75): -0.24311342716018713
cos(11.00):  0.00442561914678663
*)

value "approx_cos_trans [Ivl (-1) 1]"
value "approx_cos_trans [Ivl 1 3]"
value "approx_cos_trans [Ivl 3 5]"
value "approx_cos_trans [Ivl 5 7]"
value "approx_cos_trans [Ivl 7 9]"
value "approx_cos_trans [Ivl 9 11]"

value "approx_cos_best [Ivl (-1) 1]"
value "approx_cos_best [Ivl 1 3]"
value "approx_cos_best [Ivl 3 5]"
value "approx_cos_best [Ivl 5 7]"
value "approx_cos_best [Ivl 7 9]"
value "approx_cos_best [Ivl 9 11]"

value "approx_cos_error [Ivl (-11) (-9)]"
value "approx_cos_naive [Ivl (-11) (-9)]"
value "approx_cos_trans [Ivl (-11) (-9)]"
value "approx_cos_best [Ivl (-11) (-9)]"

value "the (compute_tm 32 10 [Ivl (-1) 1] [0] (Cos (Var 0)))"
value "the (compute_tm 32 10 [Ivl (-1) 1] [0] (Cos (Add (Var 0) (Mult (Num 2) Pi))))"
value "the (compute_tm 32 10 [Ivl 9 11] [10] (Cos (Var 0)))"
value "the (compute_tm 32 10 [Ivl (-10) 10] [0] (Cos (Var 0)))"
value "the (compute_tm 32 10 [Ivl (-1) 1] [0] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_tm 32 10 [Ivl 1 3] [2] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_tm 32 10 [Ivl 9 11] [10] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_tm 32 10 [Ivl (-1) 1] [0] (Add (Power (Cos (Add (Var 0) (Num (-2)))) 2) (Power (Sin (Add (Var 0) (Num (-2)))) 2)))"
value "the (compute_tm 32 10 [Ivl 1 3] [2] (Add (Power (Cos (Add (Var 0) (Num (-2)))) 2) (Power (Sin (Add (Var 0) (Num (-2)))) 2)))"

value "the (compute_ivl_bound 32 10 [Ivl (1000) 1002] (Cos (Var 0)))"
value "the (compute_ivl_bound 32 10 [Ivl (-1) 1] (Cos (Var 0)))"
value "the (compute_ivl_bound 32 10 [Ivl (-1) 1] (Cos (Add (Var 0) (Mult (Num 2) Pi))))"
value "the (compute_ivl_bound 32 10 [Ivl 9 11] (Cos (Var 0)))"
value "the (compute_ivl_bound 32 10 [Ivl (-10) 10] (Cos (Var 0)))"
value "the (compute_ivl_bound 32 10 [Ivl (-1) 1] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_ivl_bound 32 10 [Ivl 1 3] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_ivl_bound 32 10 [Ivl 9 11] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_ivl_bound 32 10 [Ivl (Float (-1) (-4)) (Float (1) (-4))] (Add (Power (Cos (Add (Var 0) (Num (-2)))) 2) (Power (Sin (Add (Var 0) (Num (-2)))) 2)))"
value "the (compute_ivl_bound 32 10 [Ivl 1 3] (Add (Power (Cos (Add (Var 0) (Num (-2)))) 2) (Power (Sin (Add (Var 0) (Num (-2)))) 2)))"*)

end
