import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul

/-!
# LownerHeinzCore.spectrum_convexCombo_Ioi

Topic: quantum   Node: 2c5cea53770f

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.spectrum_convexCombo_Ioi`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.spectrum_convexCombo_Ioi
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
variable [NonnegSpectrumClass ℝ 𝓐] in
lemma LownerHeinzCore.spectrum_convexCombo_Ioi {A B : 𝓐} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by simpa [sub_eq_zero] using (sub_eq_zero.mp h1t).symm
      subst ht'
      simpa [rC, h1t] using hrB
    · simpa [rC] using add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne' (sub_nonneg.mpr ht1) (by simpa using h1t)) hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (𝓐) rC ≤ C := by
    have hsum : (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB ≤ C := by
      simpa [C] using add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1)) (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB =
          algebraMap ℝ (𝓐) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx
