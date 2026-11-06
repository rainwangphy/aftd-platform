import AFTD.Prelude
import AFTD.Kb.Tcs.RowColLe

/-!
# StandardYoungTableau

Topic: combinatorics   Node: 2401dd797df0

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 2.1

For a finite diagram D : Finset (ℕ × ℕ), a standard Young tableau is an equivalence toEquiv : D ≃ Finset.Icc 1 D.card from the subtype D to the interval {1, ..., |D|} such that for all u, v : D, if row_col_le D u.1 v.1 holds then (toEquiv u : ℕ) ≤ (toEquiv v : ℕ).
-/

/-- A standard Young tableau on a diagram D is a bijection onto {1, ..., |D|} preserving the row-column order. -/
structure StandardYoungTableau (D : Finset (ℕ × ℕ)) where
  toEquiv : D ≃ Finset.Icc 1 D.card
  monotone' : ∀ (u v : D), row_col_le D u.1 v.1 → (toEquiv u : ℕ) ≤ (toEquiv v : ℕ)
