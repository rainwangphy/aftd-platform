import AFTD.Prelude

/-!
# is_positional_scoring_vector

Topic: social_choice   Node: 30446a930a04

Provenance: formalization of a published result. Source: arXiv:2610.26535 Definition 1

A scoring vector s in Q^m is a non-increasing vector of non-negative rational numbers normalized with s_1 = 1.
-/

/-- A positional scoring vector is non-increasing, non-negative, and normalized so the first place receives 1 point. -/
def is_positional_scoring_vector (m : ℕ) (s : Fin m → ℚ) : Prop :=
  (∀ i j : Fin m, i ≤ j → s j ≤ s i) ∧
  (∀ i : Fin m, 0 ≤ s i) ∧
  (∃ h : 0 < m, s ⟨0, h⟩ = 1)
