import AFTD.Prelude

/-!
# op1370_singleton_schur_formula

Topic: combinatorics   Node: e01d115dd757

Provenance: helper lemma.

The scalar inverse-matrix response of a singleton matrix is its sign divided by its weight plus its sign.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_singleton_schur_formula
    {K : Type*} [Field K] (a s : K) :
    (fun _ : Fin 1 => (1 : K)) ⬝ᵥ
      ((!![a + s] : Matrix (Fin 1) (Fin 1) K)⁻¹.mulVec ![s]) = s / (a + s) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.det_fin_one_of, Matrix.adjugate_fin_one,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, Fin.sum_univ_one, div_eq_mul_inv, mul_comm]
