theory Experiments
imports Taylor_Models
begin


(* Performance tests on taylor models. We compute range bounds on a floatarith expression and
   compare the results and execution time of taylor models with standard interval arithmetic.  
            n - The number of recursive subdivisions on the domain, i.e. a total of 2^n subdivision.
         prec - The floating point precision.
   expression - The floatarith expression used.
       domain - The domain we test on. 
     tm_order - Order of the taylor models generated. *)
definition "n = 3"
definition "prec = 64"
definition "expression = (Add (Power (Cos (Var 0)) 2) (Power (Sin (Var 0)) 2))"
definition "domain = [Ivl 0 10]"
definition "tm_order = 7"

definition "test_ia (u::unit) = compute_bound_fa_via_ia prec n expression domain"
definition "test_tm (u::unit) = compute_bound_fa_via_tm' prec tm_order n expression domain"

ML \<open>val test_ia = @{code test_ia}\<close>
ML \<open>val test_tm = @{code test_tm}\<close>

value "test_ia ()"
value "test_tm ()"

ML \<open>Timing.timeit test_ia\<close>
ML \<open>Timing.timeit test_tm\<close>

(* The caprasse example from file thys/Affine_Arithmetic/Ex_Ineqs.thy in the AFP.  *)
definition "caprasse = (\<lambda>x1 x2 x3 x4::real.
  (- x1 * x3 * x3 * x3 + 4 * x2 * x3 * x3 * x4 +
    4 * x1 * x3 * x4 * x4 + 2 * x2 * x4 * x4 * x4 + 4 * x1 * x3 + 4 * x3 * x3 + - 10 * x2 * x4 +
    -10 * x4 * x4 + 2))"
definition "caprasse_fa =
  (floatarith.Add
       (floatarith.Add
         (floatarith.Add
           (floatarith.Add
             (floatarith.Add
               (floatarith.Add
                 (floatarith.Add
                   (floatarith.Add
                     (Mult (Mult (Mult (Minus (Var 0)) (Var (Suc (Suc 0))))
                             (Var (Suc (Suc 0))))
                       (Var (Suc (Suc 0))))
                     (Mult (Mult (Mult (Mult (Num (Float 4 0)) (Var (Suc 0))) (Var (Suc (Suc 0))))
                             (Var (Suc (Suc 0))))
                       (Var 3)))
                   (Mult (Mult (Mult (Mult (Num (Float 4 0)) (Var 0)) (Var (Suc (Suc 0))))
                           (Var 3))
                     (Var 3)))
                 (Mult (Mult (Mult (Mult (Num (Float 2 0)) (Var (Suc 0))) (Var 3)) (Var 3)) (Var 3)))
               (Mult (Mult (Num (Float 4 0)) (Var 0)) (Var (Suc (Suc 0)))))
             (Mult (Mult (Num (Float 4 0)) (Var (Suc (Suc 0)))) (Var (Suc (Suc 0)))))
           (Mult (Mult (Minus (Num (Float 10 0))) (Var (Suc 0))) (Var 3)))
         (Mult (Mult (Minus (Num (Float 10 0))) (Var 3)) (Var 3)))
       (Num (Float 2 0)))
"

lemma "interpret_floatarith caprasse_fa [x\<^sub>1, x\<^sub>2, x\<^sub>3, x\<^sub>4] = caprasse x\<^sub>1 x\<^sub>2 x\<^sub>3 x\<^sub>4"
by (simp add: caprasse_fa_def caprasse_def power2_eq_square)

definition "domain2 = (\<lambda>d. [d, d, d, d]) (Ivl (-10) 10)"
  
definition "test_ia2 (u::unit) = compute_bound_fa_via_ia prec n caprasse_fa domain2"
definition "test_tm2 (u::unit) = compute_bound_fa_via_tm' prec tm_order n caprasse_fa domain2"

ML \<open>val test_ia2 = @{code test_ia2}\<close>
ML \<open>val test_tm2 = @{code test_tm2}\<close>

value "test_ia2 ()"
value "test_tm2 ()"

ML \<open>Timing.timeit test_ia2\<close>
ML \<open>Timing.timeit test_tm2\<close>

end
