import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasJointPatternProb
import AFTD.Kb.Tcs.CyclicRotateLeft
import AFTD.Kb.Tcs.DualMelasPatternCount

/-!
# dual_melas_joint_pattern_prob_nonneg

Topic: information   Node: d81e254b2984

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any field F finite-dimensional over ZMod 2, natural number k, elements α, c ∈ F, and natural numbers a, b, dual_melas_joint_pattern_prob k α c a b is nonnegative.
-/

/-- The joint pattern probability in the dual Melas sequence is nonnegative. -/
theorem dual_melas_joint_pattern_prob_nonneg
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (α c : F) (a b : ℕ) :
    0 ≤ dual_melas_joint_pattern_prob k α c a b := by
  unfold dual_melas_joint_pattern_prob
  positivity
