import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionGeneralizedPerspective
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrt
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHInvSqrt
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
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
# GeneralizedPerspectiveFunction.generalizedPerspective_neg

Topic: quantum   Node: 425be5152cd6

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.generalizedPerspective_neg`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.generalizedPerspective_neg
-/

set_option quotPrecheck false
open GeneralizedPerspectiveFunction
local infixl:70 " Δ " => GeneralizedPerspective

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GeneralizedPerspectiveFunction in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
lemma GeneralizedPerspectiveFunction.generalizedPerspective_neg
    (f h : ℝ → ℝ) (A B : L ℋ) :
    ((fun x : ℝ ↦ -f x) Δ h) A B = -((f Δ h) A B) := by
  simp [GeneralizedPerspective, cfcR, cfc_neg, mul_assoc]
