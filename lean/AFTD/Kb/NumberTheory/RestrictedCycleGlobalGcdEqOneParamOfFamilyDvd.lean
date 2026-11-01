import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcdDvdOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamGcd

/-!
# restricted_cycle_global_gcd_eq_one_param_of_family_dvd

Topic: elementary_number_theory   Node: f4183385cc02

Provenance: helper lemma. step towards global_gcd_agreement_r_three_eq

If the one-parameter gcd G_3(n) divides the restricted count a_S(n) attached to every set S = {1,2,3} ∪ T of the excluded family, then the global gcd g_3(n) equals G_3(n).
-/

/-- Family-divisibility criterion: G_3(n) dividing every excluded-family count forces g_3(n) = G_3(n). -/
theorem restricted_cycle_global_gcd_eq_one_param_of_family_dvd (n : ℕ) (h : ∀ S ∈ restricted_cycle_excluded_family 3 n, restricted_cycle_one_param_gcd 3 n ∣ restricted_cycle_perms_count n S) : restricted_cycle_global_gcd 3 n = restricted_cycle_one_param_gcd 3 n := by
  exact Nat.dvd_antisymm (restricted_cycle_global_gcd_dvd_one_param_gcd 3 n) (Finset.dvd_gcd_iff.mpr h)
