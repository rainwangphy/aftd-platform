import AFTD.Prelude

/-!
# swf_lower_restricted_dominance

Topic: social_choice   Node: a8135d2d55c9

Provenance: formalization of a published result. Source: arXiv:2610.38824 after Proposition 1

A social welfare function W on infinite utility streams in [0, 1] satisfies lower restricted dominance if for all a < b in [0, 1], W(Stream'.const a) < W(Stream'.cons b (Stream'.const a)).
-/

/-- A social welfare function satisfies lower restricted dominance if raising the first period utility above a constant tail strictly increases welfare. -/
def swf_lower_restricted_dominance (W : Stream' (Set.Icc (0 : ℝ) 1) → ℝ) : Prop :=
  ∀ a b : Set.Icc (0 : ℝ) 1, a < b →
    W (Stream'.const a) < W (Stream'.cons b (Stream'.const a))
