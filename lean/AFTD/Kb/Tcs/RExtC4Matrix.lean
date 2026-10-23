import AFTD.Prelude

/-!
# r_ext_c4_matrix

Topic: combinatorics   Node: f81d8642f79f

Provenance: formalization of a published result. Source: arXiv:2610.13987, line 131

For any natural number r, the (r + 2) by 4 boolean matrix (with entries in Bool) representing the incidence matrix of the r-extension of the 4-cycle, whose entry at row i and column j is true if i.val < r - 2, and otherwise true if (i.val - (r - 2)) % 4 equals j.val or (j.val + 1) % 4, and false otherwise.
-/

/-- The (r+2) x 4 boolean incidence matrix of the r-extension of C_4. -/
def r_ext_c4_matrix (r : ℕ) : Matrix (Fin (r + 2)) (Fin 4) Bool :=
  fun i j =>
    if i.val < r - 2 then true
    else
      let row_idx := (i.val - (r - 2)) % 4
      (row_idx == j.val) || (row_idx == (j.val + 1) % 4)
