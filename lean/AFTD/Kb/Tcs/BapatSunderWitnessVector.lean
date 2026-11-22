import AFTD.Prelude

/-!
# bapat_sunder_witness_vector

Topic: combinatorics   Node: 6b057d0c598b

Provenance: helper lemma. step towards op_1992_real_bapat_sunder_counterexample_rank_two_or_three

The explicit integer witness vector x of length 28, of squared norm 3591, for which the Bapat-Sunder quadratic form of the witness Gram matrix exceeds the permanent times x . x.
-/

/-- The integer test vector `x` of the order-28 Bapat–Sunder witness, with `x ⬝ᵥ x = 3591`. -/
def bapat_sunder_witness_vector : Fin 28 → ℤ := ![1, 15, -4, -16, 8, 18, -10, 27, -6, -18, -3, 0, 13, -1, 2, -18, -1, -9, 0, -5, 24, -4, -5, -11, 5, -7, -3, 9]
