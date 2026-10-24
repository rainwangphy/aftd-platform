import AFTD.Prelude

/-!
# perspective_affine_hasDerivAt_zero

Topic: information   Node: 6697e15ce5f2

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Lemma 4

For Q0 > 0, the perspective t ↦ (Q0 + t Q1) f((C0 + t C1)/(Q0 + t Q1)) has derivative Q1 f(C0/Q0) + (C1 Q0 - C0 Q1) f'(C0/Q0)/Q0 at 0.
-/

theorem perspective_affine_hasDerivAt_zero (f f1 : ℝ → ℝ) (Q0 Q1 C0 C1 : ℝ) (hQ : 0 < Q0)
    (hf : HasDerivAt f (f1 (C0 / Q0)) (C0 / Q0)) :
    HasDerivAt (fun t : ℝ => (Q0 + t * Q1) * f ((C0 + t * C1) / (Q0 + t * Q1)))
      (Q1 * f (C0 / Q0) + (C1 * Q0 - C0 * Q1) * f1 (C0 / Q0) / Q0) 0 := by
  have hQt : HasDerivAt (fun t : ℝ => Q0 + t * Q1) Q1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const Q1).const_add Q0
  have hCt : HasDerivAt (fun t : ℝ => C0 + t * C1) C1 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const C1).const_add C0
  have hdiv := hCt.fun_div hQt (by simp; exact hQ.ne')
  have hf' : HasDerivAt f (f1 (C0 / Q0)) ((fun t : ℝ => (C0 + t * C1) / (Q0 + t * Q1)) 0) := by
    simpa using hf
  have hcomp := hf'.comp (h := fun t : ℝ => (C0 + t * C1) / (Q0 + t * Q1)) 0 hdiv
  have := hQt.fun_mul hcomp
  exact this.congr_deriv (by
    simp only [zero_mul, add_zero, Function.comp_apply, Pi.sub_apply, sub_self]
    field_simp
    try ring)
