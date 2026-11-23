import AFTD.Prelude

/-!
# is_box

Topic: combinatorics   Node: fdbc1ac00c03

Provenance: formalization of a published result. Source: arXiv:2611.17378, Section 1

A finset of points in `Fin d → Fin n` is a box if it is the Cartesian product of 2-element subsets of `Fin n` across all coordinates `i : Fin d`.
-/

/-- A box in `Fin d → Fin n` is the Cartesian product of two-element subsets in each coordinate. -/
def is_box (d : ℕ) {n : ℕ} (B : Finset (Fin d → Fin n)) : Prop := ∃ A : Fin d → Finset (Fin n), (∀ i : Fin d, (A i).card = 2) ∧ B = Fintype.piFinset A
