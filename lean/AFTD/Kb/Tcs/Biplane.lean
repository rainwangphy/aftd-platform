import AFTD.Prelude

/-!
# Biplane

Topic: combinatorics   Node: e7f5f505815a

Provenance: formalization of a published result. Source: arXiv:2611.17855, Section 2.2

A biplane is a symmetric 2-(v, k, 2) design: a finite incidence structure of points and lines where each line contains k points, each point lies on k lines, any two distinct lines intersect in exactly 2 points, and any two distinct points lie on exactly 2 lines.
-/

/-- A biplane is a symmetric 2-(v, k, 2) design. -/
structure Biplane (P L : Type*) [Fintype P] [Fintype L] where
  inc : P → L → Prop
  k : ℕ
  points_per_line : ∀ l : L, Nat.card { p : P // inc p l } = k
  lines_per_point : ∀ p : P, Nat.card { l : L // inc p l } = k
  lines_inter_two : ∀ l₁ l₂ : L, l₁ ≠ l₂ → Nat.card { p : P // inc p l₁ ∧ inc p l₂ } = 2
  points_inter_two : ∀ p₁ p₂ : P, p₁ ≠ p₂ → Nat.card { l : L // inc p₁ l ∧ inc p₂ l } = 2
