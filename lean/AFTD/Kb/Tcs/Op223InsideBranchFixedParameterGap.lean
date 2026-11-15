import AFTD.Prelude

/-!
# op223_inside_branch_fixed_parameter_gap

Topic: graphs   Node: 6a66e280d365

Provenance: helper lemma. Scalar reduction for the weighted homotopy in Open Problem 6.1, https://arxiv.org/abs/2610.17078.

At a tied resolvent maximum inside the moved branch, the fixed-spectral-parameter derivative of the root-minus-competitor gap is positive under the displayed Schur-complement and positive-definiteness inequalities. This scalar result does not control the derivative of the spectral radius.
-/

set_option maxHeartbeats 800000

theorem op223_inside_branch_fixed_parameter_gap (t d a b C k f : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hC : 0 < C)
    (hd : 0 < d) (ha : 0 < a) (hda : a < d)
    (hdet : a ^ 2 < d * b) (hCauchy : f ^ 2 ≤ C * k)
    (htie : d = k + f ^ 2 * (t * (t*d+(1-t)*a)+(1-t)*(t*a+(1-t)*b))) :
    C * (d-a) * (t*d+(1-t)*a) -
      f ^ 2 * ((t*d+(1-t)*a) - (t*a+(1-t)*b)) *
        (1+C*(t*(t*d+(1-t)*a)+(1-t)*(t*a+(1-t)*b))) > 0 := by
  let p := t*d+(1-t)*a
  let q := t*a+(1-t)*b
  let s := t*p+(1-t)*q
  have hp : 0 < p := by
    dsimp [p]
    have h1 : 0 ≤ t*d := mul_nonneg ht0 (le_of_lt hd)
    have h2 : 0 < (1-t)*a := mul_pos (by linarith) ha
    linarith
  have hs : d = k + f ^ 2 * s := htie
  change 0 < C * (d-a) * p - f ^ 2 * (p-q) * (1+C*s)
  by_cases hm : 0 ≤ p-q
  · have h1 : 0 < C * (1-t) * (d*b-a^2) := by positivity
    have h2 : 0 ≤ (p-q) * (C*k-f^2) := mul_nonneg hm (by linarith)
    have hid : C * (d-a) * p - f ^ 2 * (p-q) * (1+C*s) =
        C * (1-t) * (d*b-a^2) + (p-q) * (C*k-f^2) := by
      have hfirst : C * (d-a) * p - f ^ 2 * (p-q) * (1+C*s) =
          C * (d*q-a*p) + (p-q) * (C*(d-f^2*s)-f^2) := by ring
      have hsecond : d*q-a*p = (1-t)*(d*b-a^2) := by
        dsimp [p,q]
        ring
      have hthird : d-f^2*s=k := by linarith [hs]
      rw [hsecond, hthird] at hfirst
      simpa only [mul_assoc] using hfirst
    rw [hid]
    linarith
  · have h1 : 0 < C*(d-a)*p := by positivity
    have h2 : f^2*(p-q)*(1+C*s) ≤ 0 := by
      have hq : 0 ≤ q := by
        dsimp [q]
        have hdb : 0 < d * b := lt_of_le_of_lt (sq_nonneg a) hdet
        have hb : 0 < b := (mul_pos_iff_of_pos_left hd).mp hdb
        positivity
      have hsp : 0 ≤ s := by
        dsimp [s]
        positivity
      have hfactor : 0 ≤ 1+C*s := by positivity
      have hneg : p-q < 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg f) (le_of_lt hneg)) hfactor
    linarith
