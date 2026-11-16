import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370AdjugateBilinearNeZero

/-!
# op1370_adjugate_bilinear_map_ne_zero

Topic: combinatorics   Node: 96761525c933

Provenance: helper lemma.

An injective field specialization preserves the nonzero adjugate bilinear form when its dot product is nonzero.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_adjugate_bilinear_map_ne_zero
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (J : Matrix ι ι ℚ) (f : ℚ[X] →+* K) (hf : Function.Injective f)
    (u v : ι → ℚ) (h : (∑ a, u a * v a) ≠ 0) :
    let A : Matrix ι ι K :=
      ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
    (fun a => f (Polynomial.C (u a))) ⬝ᵥ
      (A.adjugate.mulVec (fun a => f (Polynomial.C (v a)))) ≠ 0 := by
  classical
  dsimp only
  let P : Matrix ι ι ℚ[X] :=
    (Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C
  have hp : (∑ a, ∑ b, Polynomial.C (u a) * P.adjugate a b * Polynomial.C (v b)) ≠ 0 :=
    op1370_adjugate_bilinear_ne_zero J u v h
  have hmap : f (∑ a, ∑ b, Polynomial.C (u a) * P.adjugate a b * Polynomial.C (v b)) =
      (fun a => f (Polynomial.C (u a))) ⬝ᵥ
        ((P.map f).adjugate.mulVec (fun a => f (Polynomial.C (v a)))) := by
    have hadj : (P.map f).adjugate = P.adjugate.map f := by
      simpa only [RingHom.mapMatrix_apply] using (f.map_adjugate P).symm
    rw [hadj]
    simp only [map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply,
      Finset.mul_sum, mul_assoc]
  rw [← hmap]
  intro hz
  apply hp
  apply hf
  simpa using hz
