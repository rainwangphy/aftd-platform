import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHalfMulRealAddHalfMulRealEq
import AFTD.Kb.Tcs.JensenOperatorInequalityHalfAddHalfEq
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
# JensenOperatorInequality.rightEval_bottomRight_scalar

Topic: quantum   Node: 62cc094c57a4

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.rightEval_bottomRight_scalar`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.rightEval_bottomRight_scalar
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.rightEval_bottomRight_scalar
    (r : ℝ) (R1 X T : L ℋ) :
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1)))) =
      (R1 * T * R1) + r • (X * star X) := by
  have hS :
      (2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X) = r • (X * star X) := by
    simpa using half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (X * star X)
  have hT :
      (2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1)) =
        R1 * (T * R1) := by
    simpa using half_add_half_eq (ℋ := ℋ) (R1 * (T * R1))
  calc
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1))))
        =
      ((2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X)) +
        ((2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1))) := by
            abel
    _ = r • (X * star X) + R1 * (T * R1) := by rw [hS, hT]
    _ = (R1 * T * R1) + r • (X * star X) := by simp [mul_assoc, add_comm]
