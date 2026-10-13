import AFTD.Prelude

/-!
# lower_ones_matrix

Topic: graphs   Node: 0cb7a07e882a

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 3 (the matrix L of Proposition 3.1).

The n × n lower triangular matrix L over F₂ with all entries on and below the diagonal equal to 1: L_ij = 1 iff j ≤ i.
-/

/-- The lower triangular all-ones matrix `L` over `𝔽₂`: `L i j = 1` iff `j ≤ i`. -/
def lower_ones_matrix (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if j ≤ i then 1 else 0
