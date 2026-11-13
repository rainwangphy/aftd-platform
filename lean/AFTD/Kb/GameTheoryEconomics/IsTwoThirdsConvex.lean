import AFTD.Prelude

/-!
# is_two_thirds_convex

Topic: general_equilibrium   Node: ea0723e64c2a

Provenance: formalization of a published result. Source: arXiv:2611.16207, Definition 1

A cooperative game v : Finset α → ℝ is 2/3-convex if for every three distinct coalitions S₁, S₂, S₃, at least two of the three pairs satisfy v(Sᵢ ∪ Sⱼ) + v(Sᵢ ∩ Sⱼ) ≥ v(Sᵢ) + v(Sⱼ).
-/

/-- A cooperative game is 2/3-convex if for every three distinct coalitions, at least two pairs satisfy the supermodular inequality. -/
def is_two_thirds_convex {α : Type*} [DecidableEq α] (v : Finset α → ℝ) : Prop :=
  ∀ S₁ S₂ S₃ : Finset α, S₁ ≠ S₂ → S₁ ≠ S₃ → S₂ ≠ S₃ →
    (v (S₁ ∪ S₂) + v (S₁ ∩ S₂) ≥ v S₁ + v S₂ ∧ v (S₁ ∪ S₃) + v (S₁ ∩ S₃) ≥ v S₁ + v S₃) ∨
    (v (S₁ ∪ S₂) + v (S₁ ∩ S₂) ≥ v S₁ + v S₂ ∧ v (S₂ ∪ S₃) + v (S₂ ∩ S₃) ≥ v S₂ + v S₃) ∨
    (v (S₁ ∪ S₃) + v (S₁ ∩ S₃) ≥ v S₁ + v S₃ ∧ v (S₂ ∪ S₃) + v (S₂ ∩ S₃) ≥ v S₂ + v S₃)
