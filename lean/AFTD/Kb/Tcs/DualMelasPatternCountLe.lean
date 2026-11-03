import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasPatternCount
import AFTD.Kb.Tcs.DualMelasWindow

/-!
# dual_melas_pattern_count_le

Topic: information   Node: 603159f61433

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any field F finite-dimensional over ZMod 2, natural number k, elements α, c ∈ F, and word w : Fin k → ZMod 2, dual_melas_pattern_count k α c w ≤ 2 ^ k - 1.
-/

/-- The pattern count for any binary word in the dual Melas sequence is at most 2^k - 1. -/
theorem dual_melas_pattern_count_le
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (α c : F) (w : Fin k → ZMod 2) :
    dual_melas_pattern_count k α c w ≤ 2 ^ k - 1 := by
  unfold dual_melas_pattern_count
  exact (Finset.card_filter_le _ _).trans (by simp)
