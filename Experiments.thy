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
definition "n = 0"
definition "prec = 32"
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

end
