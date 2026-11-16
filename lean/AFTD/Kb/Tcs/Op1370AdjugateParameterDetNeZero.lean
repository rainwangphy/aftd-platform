import AFTD.Prelude

/-!
# op1370_adjugate_parameter_det_ne_zero

Topic: combinatorics   Node: e25863125ef0

Provenance: helper lemma.

The determinant of XI plus a constant matrix stays nonzero under any injective field specialization.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_adjugate_parameter_det_ne_zero
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (J : Matrix ι ι ℚ) (f : ℚ[X] →+* K) (hf : Function.Injective f) :
    (((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f).det ≠ 0 := by
  classical
  let P : Matrix ι ι ℚ[X] :=
    (Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C
  have hc : P.det.coeff (Fintype.card ι) = 1 := by
    simpa [P] using (Polynomial.coeff_det_X_add_C_card (1 : Matrix ι ι ℚ) J)
  have hp : P.det ≠ 0 := by
    intro hz
    rw [hz, Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  have hd : f P.det = (P.map f).det := by
    simpa only [RingHom.mapMatrix_apply] using (f.map_det P)
  rw [← hd]
  intro hz
  apply hp
  apply hf
  simpa using hz
