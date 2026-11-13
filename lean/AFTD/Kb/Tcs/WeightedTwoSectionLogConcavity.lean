import AFTD.Prelude

/-!
# weighted_two_section_log_concavity

Topic: combinatorics   Node: f7ed4052780d

Provenance: helper lemma. An elementary nonnegative decomposition for the one-vertex extension in OP-1399.

Two log-concave local sections, with the stated likelihood and shifted weak comparisons, give the corresponding weighted log-concavity inequality for their binary extension.
-/

theorem weighted_two_section_log_concavity (L K x xm xp y ym yp : ℝ)
    (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hx : xm * xp ≤ x ^ 2) (hy : ym * yp ≤ y ^ 2)
    (horder : xm * yp ≤ x * y)
    (hshift : xm * yp + xp * ym ≤ 2 * x * y) :
    ((L + 1) * xm + (K - 1) * ym) *
        ((L - 1) * xp + (K + 1) * yp) ≤ (L * x + K * y) ^ 2 := by
  have hLsq : 0 ≤ L ^ 2 - 1 := by nlinarith
  have hKsq : 0 ≤ K ^ 2 - 1 := by nlinarith
  have h1 : 0 ≤ (L ^ 2 - 1) * (x ^ 2 - xm * xp) :=
    mul_nonneg hLsq (sub_nonneg.mpr hx)
  have h2 : 0 ≤ (K ^ 2 - 1) * (y ^ 2 - ym * yp) :=
    mul_nonneg hKsq (sub_nonneg.mpr hy)
  have h3 : 0 ≤ 2 * (L + K) * (x * y - xm * yp) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr horder)
  have h4 : 0 ≤ (L - 1) * (K - 1) * (2 * x * y - xm * yp - xp * ym) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  apply sub_nonneg.mp
  calc
    (L * x + K * y) ^ 2 -
        ((L + 1) * xm + (K - 1) * ym) * ((L - 1) * xp + (K + 1) * yp) =
      (x - y) ^ 2 + (L ^ 2 - 1) * (x ^ 2 - xm * xp) +
      (K ^ 2 - 1) * (y ^ 2 - ym * yp) +
      2 * (L + K) * (x * y - xm * yp) +
      (L - 1) * (K - 1) * (2 * x * y - xm * yp - xp * ym) := by ring
    _ ≥ 0 := add_nonneg (add_nonneg (add_nonneg (add_nonneg (sq_nonneg (x - y)) h1) h2) h3) h4
