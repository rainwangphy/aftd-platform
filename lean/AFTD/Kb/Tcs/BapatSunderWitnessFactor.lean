import AFTD.Prelude

/-!
# bapat_sunder_witness_factor

Topic: combinatorics   Node: c5d82ee9b6dd

Provenance: helper lemma. step towards op_1992_real_bapat_sunder_counterexample_rank_two_or_three

The explicit 3 x 28 integer matrix whose 28 columns are the Gram vectors of the rank-3 witness; its first three columns have determinant -469, which is why the Gram matrix has rank 3.
-/

/-- The 3 x 28 integer factor `V` of the order-28, rank-3 Bapat–Sunder witness (Gram matrix `Vᵀ * V`). -/
def bapat_sunder_witness_factor : Matrix (Fin 3) (Fin 28) ℤ := ![![1, 2, 6, 7, -2, -3, 8, 5, -3, 8, 1, 5, 5, -4, -1, 6, -4, -7, -1, -5, -6, 0, -6, -4, 1, -5, -5, 0],
    ![2, 8, -5, 0, -6, -5, -1, 7, 0, 0, -2, 0, 4, 7, 4, 2, 6, 3, 7, 4, -6, 5, 5, -3, -7, 2, 4, 8],
    ![8, -1, 3, -3, -6, -2, 3, -1, 8, -1, 8, 8, 5, -2, 6, -5, 2, 2, -5, -3, -2, -7, 3, 8, -4, 6, -7, 1]]
