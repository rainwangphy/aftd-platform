import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily

/-!
# restricted_cycle_global_gcd

Topic: elementary_number_theory   Node: 2ffa33034352

Provenance: formalization of a published result. Source: arXiv:2610.40342 Question 14.10

The global gcd g_r(n) is the greatest common divisor of the counts restricted_cycle_perms_count n S over all sets S in restricted_cycle_excluded_family r n.
-/

/-- The global gcd g_r(n) of a_S(n) over all subsets S containing {1, ..., r}. -/
def restricted_cycle_global_gcd (r n : ℕ) : ℕ := (restricted_cycle_excluded_family r n).gcd (fun S => restricted_cycle_perms_count n S)
