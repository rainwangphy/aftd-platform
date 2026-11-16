import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370RankOneSafeSolution
import AFTD.Kb.Tcs.Op1370RankOneInjective
import AFTD.Kb.Tcs.Op1370AdjugateParameterDetNeZero

/-!
# op1370_parameter_safe_response_exists

Topic: combinatorics   Node: e07cabee03dc

Provenance: helper lemma.

A parameter matrix has a nonzero nonsingular rank-one update that preserves a nonzero updated weight and admits a response solution.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_parameter_safe_response_exists
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Infinite K]
    (J : Matrix ι ι ℚ) (f : ℚ[X] →+* K) (hf : Function.Injective f)
    (L R σ : ι → ℚ) :
    ∃ (t : K) (z : ι → K), t ≠ 0 ∧
      let A := ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
      f Polynomial.X + t * A.det ≠ 0 ∧
      Function.Injective (fun w => A.mulVec w + (t * ((fun a => f (Polynomial.C (R a))) ⬝ᵥ w)) •
        (A.det • (fun a => f (Polynomial.C (L a))))) ∧
      A.mulVec z + (t * ((fun a => f (Polynomial.C (R a))) ⬝ᵥ z)) •
        (A.det • (fun a => f (Polynomial.C (L a)))) =
        A.det • (fun a => f (Polynomial.C (σ a))) := by
  classical
  let A : Matrix ι ι K :=
    ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
  let U (v : ι → ℚ) : ι → K := fun a => f (Polynomial.C (v a))
  have hdet : A.det ≠ 0 := op1370_adjugate_parameter_det_ne_zero J f hf
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hadj (v : ι → K) : A.mulVec (A.adjugate.mulVec v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨t, z, ht, htq, hsafe, hz⟩ := op1370_rank_one_safe_solution
    A (A.det • U L) (U R) (A.det • U σ) (A.adjugate.mulVec (U σ))
    (A.adjugate.mulVec (U L)) (f Polynomial.X) A.det (hadj (U σ)) (hadj (U L)) hdet
  refine ⟨t, z, ht, hsafe, ?_, hz⟩
  exact op1370_rank_one_injective A (A.det • U L) (U R) (A.adjugate.mulVec (U L))
    t hinj (hadj (U L)) htq
