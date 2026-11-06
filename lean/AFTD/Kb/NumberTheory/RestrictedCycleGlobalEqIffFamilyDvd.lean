import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcdDvdOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily

/-!
# restricted_cycle_global_eq_iff_family_dvd

Topic: elementary_number_theory   Node: 95225fcab033

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

For every r and n, equality of the global and one-parameter gcds is equivalent to divisibility of every excluded-family count by the one-parameter gcd.
-/

theorem restricted_cycle_global_eq_iff_family_dvd (r n : ℕ) :
    restricted_cycle_global_gcd r n = restricted_cycle_one_param_gcd r n ↔
    ∀ S ∈ restricted_cycle_excluded_family r n,
      restricted_cycle_one_param_gcd r n ∣ restricted_cycle_perms_count n S := by
  constructor
  · intro h S hS
    rw [← h]
    exact Finset.gcd_dvd hS
  · intro h
    apply Nat.dvd_antisymm (restricted_cycle_global_gcd_dvd_one_param_gcd r n)
    exact Finset.dvd_gcd_iff.mpr h
