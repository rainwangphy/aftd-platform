import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremOperatorConvexOnAll
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
# JensenOperatorInequality.CondIciAll

Topic: quantum   Node: 37722f65223b

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.CondIciAll`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform localized version of Condition (i), packaged as `OperatorConvexOnAll (Set.Ici 0)` together with continuity and `f 0 ≤ 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
/-- Uniform localized version of Condition (i), packaged as `OperatorConvexOnAll (Set.Ici 0)` together with continuity and `f 0 ≤ 0`. -/
def JensenOperatorInequality.CondIciAll (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f ∧
    ContinuousOn f (Set.Ici (0 : ℝ)) ∧
    f 0 ≤ 0
