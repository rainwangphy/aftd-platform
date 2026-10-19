import AFTD.Prelude

/-!
# int_box_three

Topic: elementary_number_theory   Node: cb4bd6a31793

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 1 (boxes [[-m,m]]^d), d = 3.

The box [[-m, m]]^3 of integer vectors in ℤ^3 with every coordinate between -m and m.
-/

/-- The box `⟦-m, m⟧³` of integer vectors with every coordinate in `[-m, m]`. -/
def int_box_three (m : ℕ) : Set (Fin 3 → ℤ) :=
  {v | ∀ i, -(m : ℤ) ≤ v i ∧ v i ≤ m}
