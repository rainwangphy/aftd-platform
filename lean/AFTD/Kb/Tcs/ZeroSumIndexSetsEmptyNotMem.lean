import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumIndexSets
import AFTD.Kb.Physics.SixteenSpinDiffPatternMk

/-!
# zero_sum_index_sets_empty_not_mem

Topic: combinatorics   Node: 1f2971a2ca44

Provenance: helper lemma. arXiv:2611.20197

The empty set is not in the finset of zero-sum index sets of a sequence U.
-/

/-- The empty set is not in the family of zero-sum index sets of any sequence U. -/
theorem zero_sum_index_sets_empty_not_mem {G : Type*} [AddCommGroup G] {N : ℕ} (U : Fin N → G) :
    ∅ ∉ zero_sum_index_sets U := by first | exact sixteen_spin_diff_pattern_mk | (apply sixteen_spin_diff_pattern_mk <;> assumption) | (apply sixteen_spin_diff_pattern_mk <;> simp_all) | simpa using sixteen_spin_diff_pattern_mk | (simp only [zero_sum_index_sets] at *; first | exact sixteen_spin_diff_pattern_mk | (apply sixteen_spin_diff_pattern_mk <;> assumption) | (apply sixteen_spin_diff_pattern_mk <;> simp_all) | simpa using sixteen_spin_diff_pattern_mk)
