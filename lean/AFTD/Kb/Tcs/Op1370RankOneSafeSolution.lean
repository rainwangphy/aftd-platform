import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370ChooseSafePerturbation

/-!
# op1370_rank_one_safe_solution

Topic: combinatorics   Node: a0152264b4b7

Provenance: helper lemma.

A rank-one update has a solution while avoiding a singular update and zero reciprocal weight over an infinite field.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_rank_one_safe_solution
    {ι K : Type*} [Fintype ι] [Field K] [Infinite K]
    (A : Matrix ι ι K) (l r b x y : ι → K) (u d : K)
    (hx : A.mulVec x = b) (hy : A.mulVec y = l) (hd : d ≠ 0) :
    ∃ (t : K) (z : ι → K), t ≠ 0 ∧ 1 + t * (r ⬝ᵥ y) ≠ 0 ∧ u + t * d ≠ 0 ∧
      A.mulVec z + (t * (r ⬝ᵥ z)) • l = b := by
  let q : K := r ⬝ᵥ y
  let s : K := r ⬝ᵥ x
  obtain ⟨t, ht, hden, hsafe⟩ := op1370_choose_safe_perturbation q u d hd
  let c : K := t * s / (1 + t * q)
  refine ⟨t, x - c • y, ht, hden, hsafe, ?_⟩
  have hdot : r ⬝ᵥ (x - c • y) = s - c * q := by
    simp [s, q, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hdot, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [c]
  field_simp
  ring
