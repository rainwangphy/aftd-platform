import AFTD.Prelude

/-!
# op1370_rank_one_injective

Topic: combinatorics   Node: 928202b9f7a9

Provenance: helper lemma.

A rank-one update is injective when the corresponding scalar update factor is nonzero.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_rank_one_injective
    {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix ι ι K) (l r y : ι → K) (t : K)
    (hinj : Function.Injective A.mulVec) (hy : A.mulVec y = l)
    (htq : 1 + t * (r ⬝ᵥ y) ≠ 0) :
    Function.Injective (fun z => A.mulVec z + (t * (r ⬝ᵥ z)) • l) := by
  intro v w h
  have hvw : v + (t * (r ⬝ᵥ v)) • y = w + (t * (r ⬝ᵥ w)) • y := by
    apply hinj
    simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, hy] using h
  have hd := congrArg (fun z => r ⬝ᵥ z) hvw
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hd
  have hr : r ⬝ᵥ v = r ⬝ᵥ w := by
    apply mul_right_cancel₀ htq
    calc
      (r ⬝ᵥ v) * (1 + t * (r ⬝ᵥ y)) = (r ⬝ᵥ v) + (t * (r ⬝ᵥ v)) * (r ⬝ᵥ y) := by ring
      _ = (r ⬝ᵥ w) + (t * (r ⬝ᵥ w)) * (r ⬝ᵥ y) := hd
      _ = (r ⬝ᵥ w) * (1 + t * (r ⬝ᵥ y)) := by ring
  rw [hr] at hvw
  exact add_right_cancel hvw
