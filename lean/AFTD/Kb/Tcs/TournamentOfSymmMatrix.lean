import AFTD.Prelude

/-!
# tournament_of_symm_matrix

Topic: graphs   Node: 8ce8d60a8215

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 2.2 / Proposition 3.1 (the tournament T(G) of a symmetric matrix).

The tournament T(G) of a symmetric n × n matrix G over F₂, on vertices 1, …, n: for i < j the arc goes i → j if G_ij = 0 and j → i if G_ij = 1.
-/

/-- The tournament `T(G)` of a matrix over `𝔽₂`: for `i < j` the arc is `i → j` when
`G i j = 0` and `j → i` when `G i j = 1`. -/
def tournament_of_symm_matrix {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Digraph (Fin n) where
  Adj i j := (i < j ∧ G i j = 0) ∨ (j < i ∧ G j i = 1)
