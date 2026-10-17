import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOp
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonal
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalEqBlockOp
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpMul
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
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequality.blockOp_mul_blockDiagonal_zero_right

Topic: quantum   Node: 63d19b864f85

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.blockOp_mul_blockDiagonal_zero_right`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.blockOp_mul_blockDiagonal_zero_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
omit [CompleteSpace ℋ] in
lemma JensenOperatorInequality.blockOp_mul_blockDiagonal_zero_right
    (P00 P01 P10 P11 A Q00 Q01 Q10 Q11 : L ℋ) :
    blockOp (ℋ := ℋ) P00 P01 P10 P11 * blockDiagonal (ℋ := ℋ) 0 A *
        blockOp (ℋ := ℋ) Q00 Q01 Q10 Q11 =
      blockOp (ℋ := ℋ)
        (P01 * A * Q10)
        (P01 * A * Q11)
        (P11 * A * Q10)
        (P11 * A * Q11) := by
  rw [blockDiagonal_eq_blockOp, blockOp_mul, blockOp_mul]
  simp [mul_assoc, add_comm]
