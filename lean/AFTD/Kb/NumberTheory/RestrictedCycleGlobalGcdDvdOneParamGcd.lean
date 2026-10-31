import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamFamilySubsetExcludedFamily
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamFamily
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily

/-!
# restricted_cycle_global_gcd_dvd_one_param_gcd

Topic: elementary_number_theory   Node: 2fec5a936dba

Provenance: formalization of a published result. Source: arXiv:2610.40342 Theorem 5.1

For all r and n, the global gcd restricted_cycle_global_gcd r n divides the one-parameter gcd restricted_cycle_one_param_gcd r n.
-/

/-- The global gcd g_r(n) divides the one-parameter gcd G_r(n). -/
theorem restricted_cycle_global_gcd_dvd_one_param_gcd (r n : ℕ) :
    restricted_cycle_global_gcd r n ∣ restricted_cycle_one_param_gcd r n := by
  unfold restricted_cycle_global_gcd restricted_cycle_one_param_gcd
  exact Finset.gcd_mono (restricted_cycle_one_param_family_subset_excluded_family r n)
