import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370RankOneSensitivity

/-!
# op1370_rank_one_adjugate_sensitivity

Topic: combinatorics   Node: 6e2e88354211

Provenance: helper lemma.

A rank-one perturbation changes an adjugate-based scalar observable when its determinant and two response factors are nonzero.
-/

open Matrix Polynomial
open scoped BigOperators

theorem op1370_rank_one_adjugate_sensitivity
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (A : Matrix ι ι K) (l r w b z : ι → K) (t : K)
    (hA : A.det ≠ 0)
    (hz : A.mulVec z + (t * (r ⬝ᵥ z)) • (A.det • l) = A.det • b)
    (ht : t ≠ 0)
    (hwy : w ⬝ᵥ (A.adjugate.mulVec l) ≠ 0)
    (hrx : r ⬝ᵥ (A.adjugate.mulVec b) ≠ 0) :
    w ⬝ᵥ z ≠ w ⬝ᵥ (A.adjugate.mulVec b) := by
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))
  have hadj (v : ι → K) : A.mulVec (A.adjugate.mulVec v) = A.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact op1370_rank_one_sensitivity A (A.det • l) r w (A.det • b)
    (A.adjugate.mulVec b) (A.adjugate.mulVec l) z t hinj (hadj b) (hadj l) hz ht hwy hrx
