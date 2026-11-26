import AFTD.Prelude

/-!
# qutrit_cyclic_cubic_nonnegative

Topic: quantum   Node: 67ebd31665b4

Provenance: helper lemma. OP-2299 zero-Bell face witness; determinant identity 41055 and the arithmetic-geometric mean inequality.

The cyclic cubic determinant appearing in the constrained qutrit witness is nonnegative on the nonnegative octant.
-/

theorem qutrit_cyclic_cubic_nonnegative (p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ p^2*r + p*q^2 + q*r^2 - 3*p*q*r := by
  have core (p q r : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (_hpr : p ≤ r) :
      0 ≤ p^2*r + p*q^2 + q*r^2 - 3*p*q*r := by
    have hquad : 0 ≤ (q-p)^2 - (q-p)*(r-p) + (r-p)^2 := by
      nlinarith [sq_nonneg ((q-p)-(r-p)), sq_nonneg (q-p), sq_nonneg (r-p)]
    have h₁ := mul_nonneg hp hquad
    have h₂ := mul_nonneg (sub_nonneg.mpr hpq) (sq_nonneg (r-p))
    nlinarith [h₁, h₂]
  rcases le_total p q with hpq | hqp
  · rcases le_total p r with hpr | hrp
    · exact core p q r hp hpq hpr
    · have h := core r p q hr hrp (le_trans hrp hpq)
      nlinarith [h]
  · rcases le_total q r with hqr | hrq
    · have h := core q r p hq hqr hqp
      nlinarith [h]
    · have h := core r p q hr (le_trans hrq hqp) hrq
      nlinarith [h]
