import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul

/-!
# GeneralizedPerspectiveFunction.spectrum_convexCombo_Ioi

Topic: quantum   Node: e159468fa092

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.spectrum_convexCombo_Ioi`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.spectrum_convexCombo_Ioi
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
lemma GeneralizedPerspectiveFunction.spectrum_convexCombo_Ioi {A B : L ℋ} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht1) (Ne.symm h1t)
      simpa [rC] using
        add_pos_of_pos_of_nonneg (mul_pos h1t_pos hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB ≤ C := by
      simpa [C] using
        add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx
