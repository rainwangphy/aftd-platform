import AFTD.Prelude

/-!
# op1370_solution_schur_difference

Topic: combinatorics   Node: 2ad288b33e28

Provenance: helper lemma.

A difference between scaled solution vectors implies a difference between the corresponding inverse-matrix scalar responses.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_solution_schur_difference
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (A B : Matrix ι ι K) (b w z : ι → K)
    (hdet : A.det ≠ 0) (hB : Function.Injective B.mulVec)
    (hz : B.mulVec z = A.det • b)
    (hdiff : w ⬝ᵥ z ≠ w ⬝ᵥ (A.adjugate.mulVec b)) :
    w ⬝ᵥ (B⁻¹.mulVec b) ≠ w ⬝ᵥ (A⁻¹.mulVec b) := by
  have haunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hbunit : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hB)
  have hainj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr haunit)
  have hAsol : A.mulVec (A⁻¹.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A haunit, Matrix.one_mulVec]
  have hBsol : B.mulVec (B⁻¹.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hbunit, Matrix.one_mulVec]
  have hz' : z = A.det • (B⁻¹.mulVec b) := by
    apply hB
    rw [hz, Matrix.mulVec_smul, hBsol]
  have ha' : A.adjugate.mulVec b = A.det • (A⁻¹.mulVec b) := by
    apply hainj
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_smul, hAsol]
  intro he
  apply hdiff
  rw [hz', ha', dotProduct_smul, dotProduct_smul, he]
