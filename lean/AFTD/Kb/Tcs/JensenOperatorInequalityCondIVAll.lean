import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityCondIV
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
# JensenOperatorInequality.CondIVAll

Topic: quantum   Node: 9909872855c3

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.CondIVAll`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequality.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform version of Condition (iv), with the Hilbert space arbitrary in the same universe. This is the theorem-level uniform counterpart to the operator-level `...All` predicates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
/-- Uniform version of Condition (iv), with the Hilbert space arbitrary in the same universe. This is the theorem-level uniform counterpart to the operator-level `...All` predicates. -/
def JensenOperatorInequality.CondIVAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    CondIV (ℋ := K) f
