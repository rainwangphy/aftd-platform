import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleExactSupportCount
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcdEqSupportGcd
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcdDvdOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamGcd

/-!
# restricted_cycle_global_eq_iff_support_dvd

Topic: elementary_number_theory   Node: 1190b531df42

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

For every r and n, the global and one-parameter gcds are equal if and only if the one-parameter gcd divides the exact cycle-support count for every support contained in the interval r+1 through n.
-/

theorem restricted_cycle_global_eq_iff_support_dvd (r n : ℕ) :
    restricted_cycle_global_gcd r n = restricted_cycle_one_param_gcd r n ↔
    ∀ P ⊆ Finset.Icc (r+1) n,
      restricted_cycle_one_param_gcd r n ∣ restricted_cycle_exact_support_count n P := by
  constructor
  · intro h P hP
    rw [← h, restricted_cycle_global_gcd_eq_support_gcd]
    exact Finset.gcd_dvd (Finset.mem_powerset.mpr hP)
  · intro h
    apply Nat.dvd_antisymm (restricted_cycle_global_gcd_dvd_one_param_gcd r n)
    rw [restricted_cycle_global_gcd_eq_support_gcd]
    exact Finset.dvd_gcd_iff.mpr (fun P hP => h P (Finset.mem_powerset.mp hP))
