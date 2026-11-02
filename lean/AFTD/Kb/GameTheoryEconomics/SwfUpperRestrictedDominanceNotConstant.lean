import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SwfUpperRestrictedDominance

/-!
# swf_upper_restricted_dominance_not_constant

Topic: social_choice   Node: 42179fe11f19

Provenance: helper lemma. arXiv:2610.38824, Definition 4

If a social welfare function W on infinite utility streams in [0, 1] satisfies upper restricted dominance, then there exist utility streams x and y such that W(x) < W(y).
-/

/-- Upper restricted dominance implies that the social welfare function is not constant. -/
theorem swf_upper_restricted_dominance_not_constant
    (W : Stream' (Set.Icc (0 : ℝ) 1) → ℝ)
    (h : swf_upper_restricted_dominance W) :
    ∃ x y : Stream' (Set.Icc (0 : ℝ) 1), W x < W y := by
  let a : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  let b : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  have hab : a < b := by
    change (0 : ℝ) < 1
    norm_num
  exact ⟨Stream'.cons a (Stream'.const b), Stream'.const b, h a b hab⟩
