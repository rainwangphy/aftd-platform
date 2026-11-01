import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleCountZeroOrBaseOfShort
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcdDvdOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamGcd
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleOneParamFamily
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily

/-!
# restricted_cycle_global_eq_of_short

Topic: elementary_number_theory   Node: 67aa0bd90225

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

For every r and every positive n less than 2(r+1), the global restricted-cycle gcd equals its one-parameter gcd.
-/

theorem restricted_cycle_global_eq_of_short (r n : ℕ) (hn0 : 0 < n) (hn : n < 2 * (r+1)) :
    restricted_cycle_global_gcd r n = restricted_cycle_one_param_gcd r n := by
  classical
  have hbase : restricted_cycle_perms_count n (Finset.Icc 1 r) ∣
      restricted_cycle_global_gcd r n := by
    apply Finset.dvd_gcd_iff.mpr
    intro S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    rw [restricted_cycle_count_zero_or_base_of_short r n hn0 hn _ Finset.subset_union_left]
    split_ifs <;> simp
  have hone : restricted_cycle_one_param_gcd r n ∣
      restricted_cycle_perms_count n (Finset.Icc 1 r) := by
    apply Finset.gcd_dvd
    exact Finset.mem_insert_self _ _
  exact Nat.dvd_antisymm (restricted_cycle_global_gcd_dvd_one_param_gcd r n)
    (hone.trans hbase)
