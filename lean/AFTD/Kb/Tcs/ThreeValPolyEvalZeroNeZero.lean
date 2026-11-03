import AFTD.Prelude

/-!
# three_val_poly_eval_zero_ne_zero

Topic: combinatorics   Node: b4d2284af579

Provenance: helper lemma. arXiv:2610.39908, Proposition A.1 proof, Low-rank matrices with three prescribed off-diagonal values over F_p

In any field $K$, if $a, b, c \in K$ are non-zero, then $(0 - a) * (0 - b) * (0 - c) \neq 0$.
-/

/-- The polynomial (X - a)(X - b)(X - c) evaluated at 0 is non-zero when a, b, c are all non-zero. -/
theorem three_val_poly_eval_zero_ne_zero {K : Type*} [Field K] (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (0 - a) * (0 - b) * (0 - c) ≠ 0 := by
  simp only [zero_sub]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) (neg_ne_zero.mpr hb)) (neg_ne_zero.mpr hc)
