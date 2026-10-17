import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
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
# JensenOperatorInequality.complex_I_smul_real_I_smul_invTwo

Topic: quantum   Node: d23b859b5702

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.complex_I_smul_real_I_smul_invTwo`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.complex_I_smul_real_I_smul_invTwo
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
omit [CompleteSpace ℋ] in
lemma JensenOperatorInequality.complex_I_smul_real_I_smul_invTwo (r : ℝ) (T : L ℋ) :
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T =
      -((2⁻¹ : ℝ) * r) • T := by
  ext x
  have hcomm : r • (Complex.I • ((2⁻¹ : ℝ) • T x)) = Complex.I • (r • ((2⁻¹ : ℝ) • T x)) := by
    simpa using (smul_comm r (Complex.I : ℂ) ((2⁻¹ : ℝ) • T x))
  calc
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T x
        = Complex.I • (r • (Complex.I • ((2⁻¹ : ℝ) • T x))) := by
            rfl
    _ = Complex.I • (Complex.I • (r • ((2⁻¹ : ℝ) • T x))) := by
            rw [hcomm]
    _ = ((Complex.I : ℂ) * Complex.I) • (r • ((2⁻¹ : ℝ) • T x)) := by
            rw [smul_smul]
    _ = (-1 : ℂ) • (r • ((2⁻¹ : ℝ) • T x)) := by
            norm_num
    _ = (-1 : ℂ) • (((r * 2⁻¹ : ℝ)) • T x) := by
            rw [smul_smul]
    _ = -((2⁻¹ : ℝ) * r) • T x := by
            simp [neg_smul, mul_comm]
