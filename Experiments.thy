theory Experiments
imports Taylor_Models
begin
(*
(* Trying out arithmetic on intervals and polynomials with interval coefficients. *)
value "Ivl (-1::float) 1 + Ivl 0 1"
value "Ivl (-8::float) 2 + Ivl (-2) (-1)"
value "Ivl (0::real) 1 * Ivl 0 1"
value "Ivl (-10::real) 6 * Ivl (-4) 2"
value "Ivl (-1::real) 1 * Ivl 0 1"
value "Ivl (-1::float) 1 * Ivl 0 1"
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 (-6))] (poly.Add (poly.C (Ivl (Float 3 (-5)) (Float 3 (-5)))) (poly.Bound 0))"

value "compute_bound 64 (Add (Var 0) (Num 3)) [Ivl 1 2]"

value "map_option (interval_map real_of_float) (compute_bound 16 (Cos (Var 0)) [Ivl (-1) 1])"

value "map (interval_map real_of_float) (the (tmf_cs 32 10 (Ivl 0 2) 1 (Cos (Var 0))))"

(* Compute some taylor models. *)
value "the (compute_tm 32 7 [Ivl 0 2] [1] (Num 2))"
value "the (compute_tm 32 7 [Ivl 0 2] [1] (Var 0))"
value "the (compute_tm 32 7 [Ivl 0 2, Ivl 0 2] [1,1] (Add (Var 0) (Var 1)))"
value "tm_norm_poly (the (compute_tm 32 10 [Ivl (-1) 1] [0] (Cos (Var 0))))"
value [code] "tm_norm_poly (the (compute_tm 32 7 [Ivl (-1) 1, Ivl (-1) 1] [0, 0] (Add (Exp (Add (Var 0) (Var 1))) (Cos (Mult (Var 0) (Var 1))))))"

value "let I = [Ivl 1 3]; a = [2] in case (the (compute_tm 32 10 I a (Inverse (Var 0)))) of TaylorModel p e \<Rightarrow> (tm_lower_order (TaylorModel p e) 5 I a)"

value "map_option (interval_map real_of_float) (compute_ivl_bound 32 10 [Ivl (-1) 1] (Power (Cos (Var 0)) 2))"
value "map_option (interval_map real_of_float) (compute_ivl_bound 32 10 [Ivl (1) 2] (Inverse (Add (Cos (Var 0)) (Num 2))))"
value "map_option (interval_map real_of_float) (compute_ivl_bound 32 10 [Ivl (1) 2] (Inverse (Var 0)))"

(*definition "test (u::unit) = prove_pos 50 40 (FloatR 1 (-3)) (FloatR 1 (-1)) caprasse (aform_of_ivl (mk_tuple4 (- FloatR 1 (-1))) (mk_tuple4 (FloatR 1 (-1))))"*)
definition "test (u::unit) = the (compute_tm 32 7 [Ivl 0 2, Ivl 0 2] [1,1] (Add (Var 0) (Var 1)))"

ML \<open>val test = @{code test}\<close>

ML \<open>test ()\<close>
ML \<open>Timing.timeit test\<close>*)

value "the (compute_ivl_bound_naive 32 0 [Ivl (-1) 1] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"
value "the (compute_ivl_bound_naive 32 10 [Ivl (-1) 1] (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2)))"

end
