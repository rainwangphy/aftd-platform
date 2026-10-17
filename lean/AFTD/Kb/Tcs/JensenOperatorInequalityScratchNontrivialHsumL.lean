import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonal
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityInnerHsumInclHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclProjSum
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequalityScratch.nontrivial_hsumL

Topic: quantum   Node: 62a5a822b4e1

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequalityScratch.nontrivial_hsumL`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIVtoV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`L (HSum ℋ)` is nontrivial once `L ℋ` is.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
open JensenOperatorInequality in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [CompleteSpace ℋ] in
/-- `L (HSum ℋ)` is nontrivial once `L ℋ` is. -/
theorem JensenOperatorInequalityScratch.nontrivial_hsumL : Nontrivial (L (HSum ℋ)) := by
  have h_not_sub : ¬ Subsingleton ℋ := by
    intro hsub
    let _ : Subsingleton ℋ := hsub
    let _ : Subsingleton (L ℋ) := by infer_instance
    exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance))
      (inferInstance : Nontrivial (L ℋ))
  have hH_nontriv : Nontrivial ℋ := (not_subsingleton_iff_nontrivial.mp h_not_sub)
  let _ : Nontrivial ℋ := hH_nontriv
  rcases exists_pair_ne ℋ with ⟨x, y, hxy⟩
  let w : ℋ := x - y
  have hw : w ≠ 0 := sub_ne_zero.mpr hxy
  have hdiag_ne_zero : (blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 : L (HSum ℋ)) ≠ 0 := by
    intro h0
    have hz :
        blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 (hsumIncl ℋ 0 w) = 0 := by
      simp [h0]
    have hw0 : w = 0 := by
      have hz0 := congrArg (fun z : HSum ℋ => hsumProj ℋ 0 z) hz
      simpa [blockDiagonal] using hz0
    exact hw hw0
  exact ⟨0, blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0, hdiag_ne_zero.symm⟩
