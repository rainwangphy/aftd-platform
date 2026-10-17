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
# GeneralizedPerspectiveFunction.conj_le_conj

Topic: quantum   Node: 76bd0a0dbc1a

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.conj_le_conj`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.conj_le_conj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
lemma GeneralizedPerspectiveFunction.conj_le_conj {X Y T : L ℋ} (hXY : X ≤ Y) (hT : IsSelfAdjoint T) :
    T * X * T ≤ T * Y * T := by
  have hnonneg : 0 ≤ Y - X := sub_nonneg.mpr hXY
  have hconj : 0 ≤ T * (Y - X) * T := by
    simpa using hT.conjugate_nonneg hnonneg
  have hsub : T * (Y - X) * T = T * Y * T - T * X * T := by
    simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
  exact sub_nonneg.mp (by simpa [hsub] using hconj)
