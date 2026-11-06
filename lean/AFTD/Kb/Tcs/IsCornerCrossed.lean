import AFTD.Prelude

/-!
# is_corner_crossed

Topic: combinatorics   Node: c0b7e811f571

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.9

A diagram given as a finite set D : Finset (ℕ × ℕ) is corner-crossed if for any two northwest corners u, v : ℕ × ℕ of D—cells in D having no cells of D anywhere above them in the same column and no cells of D anywhere to their left in the same row—if u has strictly smaller row index than v (u.1 < v.1), then v has strictly smaller column index than u (v.2 < u.2).
-/

/-- A diagram is corner-crossed if any two northwest corners form a crossing (column indices strictly decrease as row indices increase). -/
def is_corner_crossed (D : Finset (ℕ × ℕ)) : Prop := ∀ ⦃u v : ℕ × ℕ⦄, (u ∈ D ∧ (∀ i < u.1, (i, u.2) ∉ D) ∧ (∀ j < u.2, (u.1, j) ∉ D)) →
                 (v ∈ D ∧ (∀ i < v.1, (i, v.2) ∉ D) ∧ (∀ j < v.2, (v.1, j) ∉ D)) →
                 u.1 < v.1 → v.2 < u.2
