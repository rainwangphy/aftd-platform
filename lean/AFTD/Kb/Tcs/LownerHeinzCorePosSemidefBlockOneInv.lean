import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR

/-!
# LownerHeinzCore.posSemidef_block_one_inv

Topic: quantum   Node: 5a83e57be337

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.posSemidef_block_one_inv`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.posSemidef_block_one_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzCore in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
variable [NonnegSpectrumClass ℝ 𝓐] in
omit [Nontrivial (𝓐)] in
omit [NonnegSpectrumClass ℝ 𝓐] in
lemma LownerHeinzCore.posSemidef_block_one_inv {A : 𝓐} (hA : IsSelfAdjoint A)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    Matrix.PosSemidef
      (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] : Matrix (Fin 2) (Fin 2) 𝓐) := by
  -- Gram matrix construction using `A^{1/2}` and `A^{-1/2}`
  set sqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) A
  set invSqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A
  set v : Fin 2 → 𝓐 := fun i => if i = 0 then sqrtA else invSqrtA
  have posV : Matrix.PosSemidef (Matrix.vecMulVec v (star v)) := by
    simpa using (Matrix.posSemidef_vecMulVec_self_star (R := 𝓐) v)
  have hsqrtA : IsSelfAdjoint sqrtA := by
    dsimp [sqrtA, cfcR]
    exact cfc_predicate _ _
  have hinvSqrtA : IsSelfAdjoint invSqrtA := by
    dsimp [invSqrtA, cfcR]
    exact cfc_predicate _ _
  have hcont_sqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have hcont_invSqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have sqrtA_mul_invSqrtA : sqrtA * invSqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_invSqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (-1) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_sqrtA : invSqrtA * sqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_sqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_invSqrtA : invSqrtA * invSqrtA = cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A := by
    dsimp [invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_invSqrt]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = -1 from by ring]
  have sqrtA_mul_sqrtA : sqrtA * sqrtA = A := by
    dsimp [sqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_sqrt]
    calc
      cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) A =
          cfcR (fun x : ℝ ↦ x) A := by
            apply cfc_congr
            intro x hx
            dsimp only
            rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 1 from by ring, Real.rpow_one]
      _ = A := cfc_id' (R := ℝ) (a := A) (ha := hA)
  have invA_eq : cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A = cfcR (fun x : ℝ ↦ x⁻¹) A := by
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (As hx)
    simpa [hxne] using (Real.rpow_neg_one x)
  have hEq : Matrix.vecMulVec v (star v) = (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] :
      Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, v, hsqrtA.star_eq, hinvSqrtA.star_eq, sqrtA_mul_sqrtA,
        sqrtA_mul_invSqrtA, invSqrtA_mul_sqrtA, invSqrtA_mul_invSqrtA, invA_eq]
  simpa [hEq] using posV
