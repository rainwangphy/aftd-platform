import AFTD.Prelude

/-!
# int_square_symmetry

Topic: elementary_number_theory   Node: 73b10f19d629

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Theorem 1 and Conjecture 1 ('up to symmetries').

The eight symmetries of the square [−m, m]² acting on ℤ²: an optional swap of the two coordinates followed by a sign on each coordinate.
-/

/-- The eight symmetries of the square. -/
def int_square_symmetry (e₁ e₂ : ℤˣ) (sw : Bool) (v : ℤ × ℤ) : ℤ × ℤ :=
  if sw then ((e₁ : ℤ) * v.2, (e₂ : ℤ) * v.1) else ((e₁ : ℤ) * v.1, (e₂ : ℤ) * v.2)
