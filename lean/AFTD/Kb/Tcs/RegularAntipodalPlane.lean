import AFTD.Prelude

/-!
# RegularAntipodalPlane

Topic: combinatorics   Node: e71b98732994

Provenance: formalization of a published result. Source: arXiv:2611.17855, Section 1 and Section 2

A regular antipodal plane of order s is a partial linear space with fixed-point-free antipodal involutions on points and lines such that each line contains s + 1 points, each point lies on s + 1 lines, antipodal pairs share no line or point, non-antipodal pairs share a unique line or point, and the involutions preserve incidence.
-/

/-- A regular antipodal plane of order s on types P and L. -/
structure RegularAntipodalPlane (P L : Type*) (s : ℕ) where
  inc : P → L → Prop
  pt_star : P → P
  line_star : L → L
  pt_star_involutive : ∀ p, pt_star (pt_star p) = p
  pt_star_ne : ∀ p, pt_star p ≠ p
  line_star_involutive : ∀ l, line_star (line_star l) = l
  line_star_ne : ∀ l, line_star l ≠ l
  inc_star : ∀ p l, inc p l ↔ inc (pt_star p) (line_star l)
  points_per_line : ∀ l : L, Nat.card {p : P // inc p l} = s + 1
  lines_per_point : ∀ p : P, Nat.card {l : L // inc p l} = s + 1
  antipodal_points_no_line : ∀ p l, inc p l → ¬ inc (pt_star p) l
  non_antipodal_points_unique_line : ∀ p q, q ≠ p → q ≠ pt_star p → ∃! l, inc p l ∧ inc q l
  antipodal_lines_no_point : ∀ p l, inc p l → ¬ inc p (line_star l)
  non_antipodal_lines_unique_point : ∀ l m, m ≠ l → m ≠ line_star l → ∃! p, inc p l ∧ inc p m
