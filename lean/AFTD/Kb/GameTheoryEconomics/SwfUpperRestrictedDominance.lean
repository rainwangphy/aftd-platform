import AFTD.Prelude

/-!
# swf_upper_restricted_dominance

Topic: social_choice   Node: 7f2178580926

Provenance: formalization of a published result. Source: arXiv:2610.38824, Definition 4

A social welfare function W on infinite utility streams in [0, 1] satisfies upper restricted dominance if for all a < b in [0, 1], W(Stream'.cons a (Stream'.const b)) < W(Stream'.const b).
-/

/-- A social welfare function satisfies upper restricted dominance if lowering the first period utility below a constant tail strictly decreases welfare. -/
def swf_upper_restricted_dominance (W : Stream' (Set.Icc (0 : ℝ) 1) → ℝ) : Prop :=
  ∀ a b : Set.Icc (0 : ℝ) 1, a < b →
    W (Stream'.cons a (Stream'.const b)) < W (Stream'.const b)
