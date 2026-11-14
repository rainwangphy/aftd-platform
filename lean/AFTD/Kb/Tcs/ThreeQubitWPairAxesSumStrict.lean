import AFTD.Prelude

/-!
# three_qubit_w_pair_axes_sum_strict

Topic: quantum   Node: 1a136eca6633

Provenance: helper lemma.

For three unit vectors, if the first two have zero W-state pair correlation, the square of the sum of their z-coordinates is strictly less than nine.
-/

theorem three_qubit_w_pair_axes_sum_strict
    (a b c : Fin 3 → ℝ)
    (ha : (∑ i, (a i)^2) = 1) (hb : (∑ i, (b i)^2) = 1)
    (hc : (∑ i, (c i)^2) = 1)
    (hab : 2*(a 0*b 0+a 1*b 1)-a 2*b 2 = 0) :
    (a 2+b 2+c 2)^2 < 9 := by
  simp [Fin.sum_univ_succ] at ha hb hc
  have aU : a 2 ≤ 1 := by nlinarith only [ha, sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2 - 1)]
  have aL : -1 ≤ a 2 := by nlinarith only [ha, sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2 + 1)]
  have bU : b 2 ≤ 1 := by nlinarith only [hb, sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2 - 1)]
  have bL : -1 ≤ b 2 := by nlinarith only [hb, sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2 + 1)]
  have cU : c 2 ≤ 1 := by nlinarith only [hc, sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2 - 1)]
  have cL : -1 ≤ c 2 := by nlinarith only [hc, sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2 + 1)]
  have hU : a 2+b 2+c 2 < 3 := by
    by_contra hh
    have ha2 : a 2 = 1 := by linarith
    have hb2 : b 2 = 1 := by linarith
    have ha0 : a 0 = 0 := by nlinarith only [ha, ha2, sq_nonneg (a 1)]
    have ha1 : a 1 = 0 := by nlinarith only [ha, ha2, sq_nonneg (a 0)]
    rw [ha2, hb2, ha0, ha1] at hab
    norm_num at hab
  have hL : -3 < a 2+b 2+c 2 := by
    by_contra hh
    have ha2 : a 2 = -1 := by linarith
    have hb2 : b 2 = -1 := by linarith
    have ha0 : a 0 = 0 := by nlinarith only [ha, ha2, sq_nonneg (a 1)]
    have ha1 : a 1 = 0 := by nlinarith only [ha, ha2, sq_nonneg (a 0)]
    rw [ha2, hb2, ha0, ha1] at hab
    norm_num at hab
  have hp : 0 < (3-(a 2+b 2+c 2))*(3+(a 2+b 2+c 2)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith only [hp]
