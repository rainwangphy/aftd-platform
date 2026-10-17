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
# JensenOperatorInequality.real_smul_complex_I_real_smul_complex_I_comm

Topic: quantum   Node: 2674bdefc172

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.real_smul_complex_I_real_smul_complex_I_comm`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.real_smul_complex_I_real_smul_complex_I_comm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
omit [CompleteSpace ℋ] in
lemma JensenOperatorInequality.real_smul_complex_I_real_smul_complex_I_comm (s r : ℝ) (T : L ℋ) :
    (s : ℝ) • Complex.I • r • Complex.I • T =
      Complex.I • r • Complex.I • (s : ℝ) • T := by
  calc
    (s : ℝ) • Complex.I • r • Complex.I • T
        = Complex.I • ((s : ℝ) • (r • (Complex.I • T))) := by
            simpa [smul_smul] using (smul_comm (s : ℝ) (Complex.I : ℂ) (r • (Complex.I • T)))
    _ = Complex.I • (r • ((s : ℝ) • (Complex.I • T))) := by
            rw [smul_comm (s : ℝ) r (Complex.I • T)]
    _ = Complex.I • (r • (Complex.I • ((s : ℝ) • T))) := by
            rw [smul_comm (s : ℝ) (Complex.I : ℂ) T]
    _ = Complex.I • r • Complex.I • (s : ℝ) • T := by
            rfl
