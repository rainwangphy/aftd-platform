import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrt
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHpowContinuousOn
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionCfcRMulEq
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
# GeneralizedPerspectiveFunction.hSqrt_mul_hSqrt_eq

Topic: quantum   Node: 905f3de230d2

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.hSqrt_mul_hSqrt_eq`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.hSqrt_mul_hSqrt_eq
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
lemma GeneralizedPerspectiveFunction.hSqrt_mul_hSqrt_eq
    {h : ℝ → ℝ} {B : L ℋ}
    (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = cfcR (ℋ := ℋ) h B := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((1 : ℝ) / 2) * (h x) ^ ((1 : ℝ) / 2) = h x := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt] using cfcR_mul_eq (ℋ := ℋ) (A := B) hsqrt hsqrt hmul
