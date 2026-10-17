import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL

/-!
# JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt

Topic: quantum   Node: 2971b14df6e9

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt {A : L ℋ} (hA : (0 : L ℋ) ≤ A) :
    cfcR (ℋ := ℋ) Real.sqrt A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA, cfcₙ_eq_cfc (f := Real.sqrt) (a := A) (hf0 := by simp), cfcR]
