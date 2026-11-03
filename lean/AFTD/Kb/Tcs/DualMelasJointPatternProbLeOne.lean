import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasJointPatternProb
import AFTD.Kb.Tcs.CyclicRotateLeft
import AFTD.Kb.Tcs.DualMelasPatternCount

/-!
# dual_melas_joint_pattern_prob_le_one

Topic: information   Node: bac0f002391d

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any field F finite-dimensional over ZMod 2, natural number k, elements α, c ∈ F, and natural numbers a, b, dual_melas_joint_pattern_prob k α c a b is at most 1.
-/

/-- The joint pattern probability in the dual Melas sequence is at most 1. -/
theorem dual_melas_joint_pattern_prob_le_one
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (α c : F) (a b : ℕ) :
    dual_melas_joint_pattern_prob k α c a b ≤ 1 := by
  unfold dual_melas_joint_pattern_prob
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [div_le_one hpos]
  norm_cast
  have hcard : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp
  have hle := Finset.card_le_univ {w | dual_melas_pattern_count k α c w = a ∧ dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b}
  omega
