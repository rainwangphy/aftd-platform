import AFTD.Prelude

/-!
# op1370_rank_one_nonsingular_solution

Topic: combinatorics   Node: b203895831b6

Provenance: helper lemma.

A nonzero nonsingular rank-one update admits a solution over any field of characteristic other than two.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_rank_one_nonsingular_solution
    {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix ι ι K) (l r b x y : ι → K)
    (hx : A.mulVec x = b) (hy : A.mulVec y = l) (h2 : (2 : K) ≠ 0) :
    ∃ (t : K) (z : ι → K), t ≠ 0 ∧ 1 + t * (r ⬝ᵥ y) ≠ 0 ∧
      A.mulVec z + (t * (r ⬝ᵥ z)) • l = b := by
  let s : K := r ⬝ᵥ x
  let q : K := r ⬝ᵥ y
  by_cases hq : q = 0
  · refine ⟨1, x - s • y, one_ne_zero, ?_, ?_⟩
    · change 1 + 1 * q ≠ 0
      simp [hq]
    · have hdot : r ⬝ᵥ (x - s • y) = s - s * q := by
        simp [s, q, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hdot, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq]
      ring
  · refine ⟨q⁻¹, x - (s / (2 * q)) • y, inv_ne_zero hq, ?_, ?_⟩
    · change 1 + q⁻¹ * q ≠ 0
      rw [inv_mul_cancel₀ hq]
      simpa only [one_add_one_eq_two] using h2
    · have hdot : r ⬝ᵥ (x - (s / (2 * q)) • y) = s - (s / (2 * q)) * q := by
        simp [s, q, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hdot, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
