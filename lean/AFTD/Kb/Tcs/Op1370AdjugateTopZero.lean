import AFTD.Prelude

/-!
# op1370_adjugate_top_zero

Topic: combinatorics   Node: 95ca17cc13be

Provenance: helper lemma.

An adjugate entry of XI plus a constant matrix has zero coefficient at the matrix dimension.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_adjugate_top_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℚ) (i j : ι) :
    (((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).adjugate i j).coeff
      (Fintype.card ι) = 0 := by
  classical
  rw [Matrix.adjugate_apply]
  have hmat :
      ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).updateRow j (Pi.single i 1) =
      (Polynomial.X : ℚ[X]) • (((1 : Matrix ι ι ℚ).updateRow j 0).map Polynomial.C) +
        ((J.updateRow j (Pi.single i 1)).map Polynomial.C) := by
    apply Matrix.ext
    intro a b
    by_cases h : a = j
    · subst a
      simp [Matrix.updateRow_apply, Pi.single_apply]
    · by_cases hab : a = b
      · subst b
        simp [Matrix.updateRow_apply, h]
      · simp [Matrix.updateRow_apply, h, hab]
  rw [hmat, Polynomial.coeff_det_X_add_C_card]
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro b
  simp [Matrix.updateRow_apply]
