import AFTD.Prelude

/-!
# op1370_rank_one_perturbed_solution

Topic: combinatorics   Node: c94282327960

Provenance: helper lemma.

Over a field of characteristic other than two, a nonzero rank-one perturbation admits a solution.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_rank_one_perturbed_solution
    {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix ι ι K) (l r b x y : ι → K)
    (hx : A.mulVec x = b) (hy : A.mulVec y = l) (h2 : (2 : K) ≠ 0) :
    ∃ (t : K) (z : ι → K), t ≠ 0 ∧
      A.mulVec z + (t * (r ⬝ᵥ z)) • l = b := by
  let s : K := r ⬝ᵥ x
  let q : K := r ⬝ᵥ y
  by_cases hq : q = 0
  · refine ⟨1, x - s • y, one_ne_zero, ?_⟩
    have hdot : r ⬝ᵥ (x - s • y) = s - s * q := by
      simp [s, q, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hdot, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq]
    ring
  · refine ⟨q⁻¹, x - (s / (2 * q)) • y, inv_ne_zero hq, ?_⟩
    have hdot : r ⬝ᵥ (x - (s / (2 * q)) • y) = s - (s / (2 * q)) * q := by
      simp [s, q, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hdot, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
