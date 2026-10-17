import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL

/-!
# GeneralizedPerspectiveFunction.cfcR_mul_eq

Topic: quantum   Node: dc22d96968d0

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.cfcR_mul_eq`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.cfcR_mul_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
lemma GeneralizedPerspectiveFunction.cfcR_mul_eq {g k m : ℝ → ℝ} {A : L ℋ}
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = m x) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = cfcR (ℋ := ℋ) m A := by
  rw [← cfc_mul (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
      (f := g) (g := k) (a := A) hg hk]
  apply cfc_congr
  intro x hx
  simpa using hmul x hx
