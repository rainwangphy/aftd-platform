import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreOperatorConvexOn
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.Tcs.LownerHeinzCoreSpectrumConvexComboIoi
import AFTD.Kb.Tcs.LownerHeinzCorePosSemidefBlockOneInv
import AFTD.Kb.Tcs.LownerHeinzCoreSchurConjEqDiagonal
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul

/-!
# LownerHeinzCore.one_div_operatorConvexOn_Ioi

Topic: quantum   Node: a77f9a856fcc

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.one_div_operatorConvexOn_Ioi`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.one_div_operatorConvexOn_Ioi
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
theorem LownerHeinzCore.one_div_operatorConvexOn_Ioi :
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  dsimp [OperatorConvexOn]
  intro A B t hA hB ht0 ht1 As Bs
  -- rewrite `1/x` as `x⁻¹`
  simp only [one_div]
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have specC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi  (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  set invA : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) A
  set invB : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) B
  set invC : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) C
  set D : 𝓐 := (1 - t) • invA + t • invB
  let M_A : Matrix (Fin 2) (Fin 2) (𝓐) := !![A, 1; 1, invA]
  let M_B : Matrix (Fin 2) (Fin 2) (𝓐) := !![B, 1; 1, invB]
  let M : Matrix (Fin 2) (Fin 2) (𝓐) := (1 - t) • M_A + t • M_B
  have posA : Matrix.PosSemidef M_A := by
    simpa [M_A, invA] using posSemidef_block_one_inv  (A := A) hA As
  have posB : Matrix.PosSemidef M_B := by
    simpa [M_B, invB] using posSemidef_block_one_inv  (A := B) hB Bs
  have posM : Matrix.PosSemidef M := by
    simpa [M] using Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul (x := M_A) (a := (1 - t)) posA (sub_nonneg.mpr ht1))
      (Matrix.PosSemidef.smul (x := M_B) (a := t) posB ht0)
  have hM : M = !![C, 1; 1, D] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [M, M_A, M_B, C]
    · have h1 : (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = (1 : 𝓐) := by
        calc
          (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = ((1 - t) + t) • (1 : 𝓐) := by
            simpa using (add_smul (1 - t) t (1 : 𝓐)).symm
          _ = (1 : 𝓐) := by simp [sub_add_cancel]
      simp [M, M_A, M_B, h1]
    · have h1 : (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = (1 : 𝓐) := by
        calc
          (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = ((1 - t) + t) • (1 : 𝓐) := by
            simpa using (add_smul (1 - t) t (1 : 𝓐)).symm
          _ = (1 : 𝓐) := by simp [sub_add_cancel]
      simp [M, M_A, M_B, h1]
    · simp [M, M_A, M_B, D]
  let U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hU : IsUnit U := by
    let V : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), invC; 0, 1]
    refine ⟨⟨U, V, ?_, ?_⟩, rfl⟩
    · dsimp [U, V]
      simp [Matrix.one_fin_two]
    · dsimp [U, V]
      simp [Matrix.one_fin_two]
  have hconj :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U
        = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
    have hInvC_sa : IsSelfAdjoint invC := by
      dsimp [invC, cfcR]
      exact cfc_predicate _ _
    have hcont_inv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (spectrum ℝ C) :=
      fun x hx => (continuousAt_inv₀ (ne_of_gt (specC hx))).continuousWithinAt
    have invC_mul_C : invC * C = (1 : 𝓐) := by
      dsimp [invC, cfcR]
      have hmul :
          cfcR (fun x : ℝ ↦ x⁻¹) C * C =
            cfcR (fun x : ℝ ↦ x⁻¹ * x) C := by
        simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
          (cfc_mul (fun x : ℝ ↦ x⁻¹) (fun x : ℝ ↦ x) C hcont_inv continuousOn_id).symm
      rw [hmul, ← cfc_const_one ℝ C]
      apply cfc_congr
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (specC hx)
      simp [hxne]
    have C_mul_invC : C * invC = (1 : 𝓐) := by
      dsimp [invC, cfcR]
      have hmul :
          C * cfcR (fun x : ℝ ↦ x⁻¹) C =
            cfcR (fun x : ℝ ↦ x * x⁻¹) C := by
        simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
          (cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x⁻¹) C continuousOn_id hcont_inv).symm
      rw [hmul, ← cfc_const_one ℝ C]
      apply cfc_congr
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (specC hx)
      simp [hxne]
    simpa [U] using
      schur_conj_eq_diagonal  (C := C) (D := D) (invC := invC)
        hInvC_sa invC_mul_C C_mul_invC
  have posDiag :
      Matrix.PosSemidef (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) := by
    have posConj : Matrix.PosSemidef (star U * M * U) := by
      simpa [Matrix.star_eq_conjTranspose] using (posM.conjTranspose_mul_mul_same U)
    have posConj' :
        Matrix.PosSemidef
          (star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) 𝓐) * U) := by
      -- rewrite the middle block matrix as `M`
      rw [← hM]
      exact posConj
    -- rewrite the goal using the computed conjugation
    rw [← hconj]
    exact posConj'
  have hinvC : invC ≤ D := by
    have hDinvC : 0 ≤ D - invC := by
      simpa using
        (Matrix.posSemidef_diagonal_iff (R := 𝓐)
          (d := fun i : Fin 2 => if i = 0 then C else D - invC)).1 posDiag (1 : Fin 2)
    exact le_of_sub_nonneg hDinvC
  exact hinvC
