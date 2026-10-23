import AFTD.Prelude

/-!
# c4_incidence_matrix

Topic: combinatorics   Node: 3ec8db5e9eea

Provenance: formalization of a published result. Source: arXiv:2610.13987, line 131

The 4 by 4 boolean matrix (with entries in Bool) whose entry at row i and column j is true if i.val = j.val or i.val = (j.val + 1) % 4, and false otherwise, representing the unoriented incidence matrix of the 4-cycle graph C_4.
-/

/-- The 4x4 boolean incidence matrix of the 4-cycle graph C_4. -/
def c4_incidence_matrix : Matrix (Fin 4) (Fin 4) Bool :=
  fun i j => (i.val == j.val) || (i.val == (j.val + 1) % 4)
