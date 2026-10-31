import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamGcd

/-!
# restricted_cycle_global_gcd_eq_one_param_gcd_3_5

Topic: elementary_number_theory   Node: 7fc8311b08b8

Provenance: formalization of a published result. Source: arXiv:2610.40342 Question 14.10

For r = 3 and n = 5, restricted_cycle_global_gcd 3 5 = restricted_cycle_one_param_gcd 3 5.
-/

/-- For r = 3 and n = 5, the global gcd and the one-parameter gcd agree. -/
theorem restricted_cycle_global_gcd_eq_one_param_gcd_3_5 :
    restricted_cycle_global_gcd 3 5 = restricted_cycle_one_param_gcd 3 5 := rfl
