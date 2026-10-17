import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOp
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpExt
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
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
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequality.blockOp_mul

Topic: quantum   Node: a26303509b5e

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.blockOp_mul`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.blockOp_mul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
set_option maxHeartbeats 400000 in
-- Multiplying two generic `blockOp` expressions is elaboration-heavy.
omit [CompleteSpace ℋ] in
lemma JensenOperatorInequality.blockOp_mul (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  -- The extra heartbeat budget stays local to this normalization lemma.
  refine blockOp_ext (ℋ := ℋ) ?_ ?_
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]
