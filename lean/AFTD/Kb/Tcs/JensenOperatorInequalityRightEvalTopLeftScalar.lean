import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHalfAddHalfEq
import AFTD.Kb.Tcs.JensenOperatorInequalityRealSmulComplexIRealSmulComplexIComm
import AFTD.Kb.Tcs.JensenOperatorInequalityComplexISmulRealISmulInvTwo
import AFTD.Kb.Tcs.JensenOperatorInequalityHalfMulRealAddHalfMulRealEq
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
# JensenOperatorInequality.rightEval_topLeft_scalar

Topic: quantum   Node: 2dc28a2f18ce

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.rightEval_topLeft_scalar`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.rightEval_topLeft_scalar
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.rightEval_topLeft_scalar
    (r : ℝ) (R0 X T : L ℋ) :
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)))) =
      star X * (T * X) + r • (R0 * R0) := by
  have hP :
      (2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X)) =
        star X * (T * X) := by
    simpa using half_add_half_eq (ℋ := ℋ) (star X * (T * X))
  have hQhalf :
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        r • (R0 * R0) := by
    have hterm :
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
          ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
      calc
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))
            = -(Complex.I • r • Complex.I • (2⁻¹ : ℝ) • (R0 * R0)) := by
                rw [real_smul_complex_I_real_smul_complex_I_comm
                  (ℋ := ℋ) (s := (2⁻¹ : ℝ)) (r := r) (T := R0 * R0)]
        _ = ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
            rw [complex_I_smul_real_I_smul_invTwo (ℋ := ℋ) (r := r) (T := R0 * R0)]
            simp
    calc
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        ((2⁻¹ : ℝ) * r) • (R0 * R0) + ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
          simp [hterm]
      _ = r • (R0 * R0) := half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (R0 * R0)
  calc
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))))
        =
      ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X))) +
        (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))) := by
            abel
    _ = star X * (T * X) + r • (R0 * R0) := by rw [hP, hQhalf]
