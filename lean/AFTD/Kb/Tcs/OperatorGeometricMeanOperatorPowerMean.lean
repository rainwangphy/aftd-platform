import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionGeneralizedPerspective
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
# OperatorGeometricMean.operatorPowerMean

Topic: quantum   Node: 5cbc8c2af3fb

Provenance: formalization of a published result. Source: QuantumInfo, `OperatorGeometricMean.operatorPowerMean`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/OperatorGeometricMean.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The operator `(α, β)`-power mean, realized as a generalized perspective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
open GeneralizedPerspectiveFunction in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The operator `(α, β)`-power mean, realized as a generalized perspective. -/
noncomputable def OperatorGeometricMean.operatorPowerMean (α β : ℝ) (A B : L ℋ) : L ℋ :=
  GeneralizedPerspective (fun x : ℝ ↦ x ^ α) (fun x : ℝ ↦ x ^ β) A B
