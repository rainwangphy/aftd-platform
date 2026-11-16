import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370RankOneAdjugateSensitivity
import AFTD.Kb.Tcs.Op1370AdjugateBilinearMapNeZero
import AFTD.Kb.Tcs.Op1370AdjugateParameterDetNeZero

/-!
# op1370_parameter_rank_one_sensitivity

Topic: combinatorics   Node: 73850d49be10

Provenance: helper lemma.

Two nonzero dot products ensure a rank-one change to a parameter matrix changes the scalar observable.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_parameter_rank_one_sensitivity
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (J : Matrix ι ι ℚ) (f : ℚ[X] →+* K) (hf : Function.Injective f)
    (l r w b : ι → ℚ) (z : ι → K) (t : K) (ht : t ≠ 0)
    (hwl : (∑ a, w a * l a) ≠ 0) (hrb : (∑ a, r a * b a) ≠ 0)
    (hz : let A := ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
      A.mulVec z + (t * ((fun a => f (Polynomial.C (r a))) ⬝ᵥ z)) •
        (A.det • (fun a => f (Polynomial.C (l a)))) =
        A.det • (fun a => f (Polynomial.C (b a)))) :
    let A := ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
    (fun a => f (Polynomial.C (w a))) ⬝ᵥ z ≠
      (fun a => f (Polynomial.C (w a))) ⬝ᵥ
        (A.adjugate.mulVec (fun a => f (Polynomial.C (b a)))) := by
  classical
  let A : Matrix ι ι K :=
    ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
  let U (v : ι → ℚ) : ι → K := fun a => f (Polynomial.C (v a))
  have hdet : A.det ≠ 0 := op1370_adjugate_parameter_det_ne_zero J f hf
  have hw : U w ⬝ᵥ (A.adjugate.mulVec (U l)) ≠ 0 :=
    op1370_adjugate_bilinear_map_ne_zero J f hf w l hwl
  have hr : U r ⬝ᵥ (A.adjugate.mulVec (U b)) ≠ 0 :=
    op1370_adjugate_bilinear_map_ne_zero J f hf r b hrb
  exact op1370_rank_one_adjugate_sensitivity A (U l) (U r) (U w) (U b) z t
    hdet hz ht hw hr
