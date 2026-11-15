import AFTD.Prelude

/-!
# is_digraphon

Topic: combinatorics   Node: 4ae4563a53dd

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 2

A function W : ℝ → ℝ → ℝ is a digraphon if for all x, y ∈ [0, 1] we have 0 ≤ W x y ∧ W x y ≤ 1, and the uncurried function Function.uncurry W is measurable on ℝ × ℝ.
-/

/-- Predicate for a function W : ℝ → ℝ → ℝ to be a digraphon on [0,1]². -/
def is_digraphon (W : ℝ → ℝ → ℝ) : Prop := (∀ x y, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ W x y ∧ W x y ≤ 1) ∧
  Measurable (Function.uncurry W)
