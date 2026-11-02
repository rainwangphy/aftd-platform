import AFTD.Prelude

/-!
# swf_is_monotone

Topic: social_choice   Node: c7fd912f1b6d

Provenance: formalization of a published result. Source: arXiv:2610.38824, Definition 1

A social welfare function W on infinite utility streams in [0, 1] is monotone if whenever stream x is pointwise greater than or equal to stream y, W(x) is greater than or equal to W(y).
-/

/-- A social welfare function is monotone if pointwise dominance implies weakly higher welfare. -/
def swf_is_monotone (W : Stream' (Set.Icc (0 : ℝ) 1) → ℝ) : Prop :=
  ∀ x y : Stream' (Set.Icc (0 : ℝ) 1), (∀ t, x t ≤ y t) → W x ≤ W y
