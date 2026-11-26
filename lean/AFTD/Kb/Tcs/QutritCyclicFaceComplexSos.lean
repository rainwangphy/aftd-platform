import AFTD.Prelude
import AFTD.Kb.Tcs.QutritCyclicFaceAlgebraicSos

/-!
# qutrit_cyclic_face_complex_sos

Topic: quantum   Node: ea2502775994

Provenance: helper lemma. OP-2299 exact dual certificate 41079 and algebraic identity 41085.

The cyclic zero-Bell product witness, multiplied by the squared norm of the second factor, equals four explicit positive-partial-transpose squares for any primitive cube root and constrained product.
-/

theorem qutrit_cyclic_face_complex_sos (w x0 x1 x2 y0 y1 y2 : ℂ)
    (hw : w^2+w+1=0) (hstar : (starRingEnd ℂ) w = -1-w)
    (hg : x0*y1+w*x1*y2+w^2*x2*y0=0) :
    (Complex.normSq y0 + Complex.normSq y1 + Complex.normSq y2) *
      ((-Complex.normSq (x0*y1+x1*y2+x2*y0) +
          Complex.normSq (x0*y1+w^2*x1*y2+w*x2*y0))/3 +
         Complex.normSq (x0*y2)+Complex.normSq (x1*y0)+Complex.normSq (x2*y1)) =
    Complex.normSq ((starRingEnd ℂ) x0*y0*y2 + w*(starRingEnd ℂ) x1*y0*y1 + w^2*(starRingEnd ℂ) x2*y1*y2) +
    Complex.normSq ((w^2*x0*(starRingEnd ℂ) y0*y1 - 2*x1*(starRingEnd ℂ) y0*y2 + w*x2*(starRingEnd ℂ) y0*y0)/3 + x2*(starRingEnd ℂ) y1*y1) +
    Complex.normSq ((w*x0*(starRingEnd ℂ) y1*y1 + w^2*x1*(starRingEnd ℂ) y1*y2 - 2*x2*(starRingEnd ℂ) y1*y0)/3 + x0*(starRingEnd ℂ) y2*y2) +
    Complex.normSq ((-2*x0*(starRingEnd ℂ) y2*y1 + w*x1*(starRingEnd ℂ) y2*y2 + w^2*x2*(starRingEnd ℂ) y2*y0)/3 + x1*(starRingEnd ℂ) y0*y0) := by
  have hwstar : (starRingEnd ℂ) w = w^2 := by
    rw [hstar]
    linear_combination -hw
  have hwstar2 : (starRingEnd ℂ) (w^2) = w := by
    rw [map_pow, hstar]
    linear_combination hw
  have hgc : (starRingEnd ℂ) x0*(starRingEnd ℂ) y1 + (starRingEnd ℂ) x1*(starRingEnd ℂ) y2*w^2 + (starRingEnd ℂ) x2*(starRingEnd ℂ) y0*w=0 := by
    have h := congrArg (starRingEnd ℂ) hg
    simp only [map_add, map_mul, map_pow, map_zero] at h
    rw [hwstar] at h
    have hw4 : (w^2)^2 = w := by
      linear_combination (w^2-w)*hw
    rw [hw4] at h
    linear_combination h
  have hcalc := qutrit_cyclic_face_algebraic_sos w x0 x1 x2 ((starRingEnd ℂ) x0) ((starRingEnd ℂ) x1) ((starRingEnd ℂ) x2) y0 y1 y2 ((starRingEnd ℂ) y0) ((starRingEnd ℂ) y1) ((starRingEnd ℂ) y2) hw (by linear_combination hg) hgc
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.normSq_eq_conj_mul_self]
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, Complex.conj_conj, hstar]
  have hw2 : w^2 = -w-1 := by linear_combination hw
  have hw3 : w^3 = 1 := by linear_combination (w-1)*hw
  have hw4 : w^4 = w := by linear_combination (w^2-w)*hw
  ring_nf at hcalc ⊢
  simp only [hw4, hw3, hw2] at hcalc ⊢
  ring_nf at hcalc ⊢
  linear_combination (1/9 : ℂ)*hcalc
