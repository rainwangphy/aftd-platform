import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreOperatorMonotoneOn
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR

/-!
# LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici

Topic: quantum   Node: 622a7b2d0f44

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici
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
theorem LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
  OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  dsimp [OperatorMonotoneOn]
  intro A B hA0 hB0 hBA hspA hspB
  have hA : cfcR (fun x : ℝ ↦ x ^ p) A = A ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := A) (y := p) (ha := hA0)).symm
  have hB : cfcR (fun x : ℝ ↦ x ^ p) B = B ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := B) (y := p) (ha := hB0)).symm
  simpa [hA, hB] using (CFC.rpow_le_rpow (A := 𝓐) hp hBA)
