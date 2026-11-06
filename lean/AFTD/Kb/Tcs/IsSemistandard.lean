import AFTD.Prelude
import AFTD.Kb.Tcs.RowColLe

/-!
# is_semistandard

Topic: combinatorics   Node: 1a2e08abf304

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 2.1

For a finite diagram D : Finset (ℕ × ℕ), a filling M : D → ℕ is semi-standard if for all u, v : D, row_col_le D u.1 v.1 implies M u ≤ M v, and row_col_le D u.1 v.1 with strictly smaller row index u.1.1 < v.1.1 implies M u < M v.
-/

/-- A filling of D is semi-standard if it is weakly increasing along the row-column order and strictly increasing across strictly increasing rows. -/
def is_semistandard (D : Finset (ℕ × ℕ)) (M : D → ℕ) : Prop := (∀ u v : D, row_col_le D u.1 v.1 → M u ≤ M v) ∧
   (∀ u v : D, row_col_le D u.1 v.1 → u.1.1 < v.1.1 → M u < M v)
