import AFTD.Prelude

/-!
# young_diagram_same_len_rows_below

Topic: combinatorics   Node: a858bfd9f3cd

Provenance: formalization of a published result. Source: arXiv:2610.29291 Theorem 3.4 proof

The number of rows in a Young diagram strictly below row $i$ that have the same length as row $i$.
-/

/-- The number of rows strictly below row i that have the same length as row i. -/
def young_diagram_same_len_rows_below (μ : YoungDiagram) (i : ℕ) : ℕ := ((Finset.range (μ.colLen 0)).filter fun k => i < k ∧ μ.rowLen k = μ.rowLen i).card
