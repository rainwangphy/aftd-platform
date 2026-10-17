import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOp
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonal
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv
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
# JensenOperatorInequality.blockOp_smulR

Topic: quantum   Node: 3c438bffa0f3

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.blockOp_smulR`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.blockOp_smulR
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
set_option synthInstance.maxHeartbeats 100000 in
-- Scalar action on `blockOp` triggers expensive instance search for nested operator expressions.
lemma JensenOperatorInequality.blockOp_smulR
    (r : ℝ) (A00 A01 A10 A11 : L ℋ) :
    r • blockOp (ℋ := ℋ) A00 A01 A10 A11 =
      blockOp (ℋ := ℋ) (r • A00) (r • A01) (r • A10) (r • A11) := by
  have coe_smul_hsum : ∀ (f : L (HSum ℋ)) (x : HSum ℋ), (r • f) x = r • (f x) := by
    intros; rfl
  have coe_smul_h : ∀ (f : L ℋ) (x : ℋ), (r • f) x = r • (f x) := by
    intros; rfl
  ext z i
  fin_cases i <;> {
    simp only [blockOp, add_apply, ContinuousLinearMap.comp_apply,
      smul_add, coe_smul_hsum, coe_smul_h]
    simp [hsumProj, hsumIncl, hsumEquiv]
  }
