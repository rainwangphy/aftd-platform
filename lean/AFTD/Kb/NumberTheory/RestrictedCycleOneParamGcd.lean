import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamFamily

/-!
# restricted_cycle_one_param_gcd

Topic: elementary_number_theory   Node: f0c08b6857d9

Provenance: formalization of a published result. Source: arXiv:2610.40342 Question 14.10

The one-parameter gcd G_r(n) is the greatest common divisor of the counts restricted_cycle_perms_count n S over all sets S in restricted_cycle_one_param_family r n.
-/

/-- The one-parameter gcd G_r(n) of a_S(n) over the family {1, ..., r, k}. -/
def restricted_cycle_one_param_gcd (r n : ℕ) : ℕ := (restricted_cycle_one_param_family r n).gcd (fun S => restricted_cycle_perms_count n S)
