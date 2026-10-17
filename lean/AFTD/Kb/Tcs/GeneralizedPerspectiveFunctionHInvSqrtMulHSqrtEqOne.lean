import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHInvSqrt
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrt
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHpowContinuousOn
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionCfcRSqEq
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# GeneralizedPerspectiveFunction.hInvSqrt_mul_hSqrt_eq_one

Topic: quantum   Node: 803b10ccda9b

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.hInvSqrt_mul_hSqrt_eq_one`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.hInvSqrt_mul_hSqrt_eq_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GeneralizedPerspectiveFunction in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
lemma GeneralizedPerspectiveFunction.hInvSqrt_mul_hSqrt_eq_one
    {h : ℝ → ℝ} {B : L ℋ}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hInvSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = (1 : L ℋ) := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hinv :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((-1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((-1 : ℝ) / 2) * (h x) ^ ((1 : ℝ) / 2) = 1 := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt, hInvSqrt] using cfcR_sq_eq (ℋ := ℋ) (A := B) hB hinv hsqrt hmul
