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
# JensenOperatorInequality.half_mul_real_add_half_mul_real_eq

Topic: quantum   Node: e2c6e1b1d2f7

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.half_mul_real_add_half_mul_real_eq`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.half_mul_real_add_half_mul_real_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
omit [CompleteSpace ℋ] in
lemma JensenOperatorInequality.half_mul_real_add_half_mul_real_eq (r : ℝ) (T : L ℋ) :
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T = r • T := by
  calc
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T =
        (((2⁻¹ : ℝ) * r) + ((2⁻¹ : ℝ) * r)) • T := by
          simp [add_smul]
    _ = r • T := by ring_nf
