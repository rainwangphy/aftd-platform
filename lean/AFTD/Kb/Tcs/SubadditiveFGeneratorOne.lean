import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFGenerator

/-!
# subadditive_f_generator_one

Topic: information   Node: c1062b552119

Provenance: helper lemma. arXiv:2610.21231, Corollary 1

The generator function f satisfies f(1) = 0.
-/

/-- The generator function f satisfies f(1) = 0. -/
theorem subadditive_f_generator_one (α : ℝ) (s : ℝ → ℝ) : subadditive_f_generator α s 1 = 0 := by
  simp [subadditive_f_generator]
