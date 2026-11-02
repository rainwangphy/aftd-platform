import AFTD.Prelude

/-!
# swf_is_stationary

Topic: social_choice   Node: cfd0d4e5dccb

Provenance: formalization of a published result. Source: arXiv:2610.38824, Definition 6

A social welfare function W on infinite utility streams in [0, 1] is stationary if whenever x and y share the same first component x 0 = y 0, W(x) ≥ W(y) if and only if W(tail x) ≥ W(tail y).
-/

/-- A social welfare function is stationary if streams sharing the first period preserve their ranking after removing the head. -/
def swf_is_stationary (W : Stream' (Set.Icc (0 : ℝ) 1) → ℝ) : Prop :=
  ∀ x y : Stream' (Set.Icc (0 : ℝ) 1), x 0 = y 0 →
    (W x ≥ W y ↔ W (Stream'.tail x) ≥ W (Stream'.tail y))
