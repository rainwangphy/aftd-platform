import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrt
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHInvSqrt
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
# GeneralizedPerspectiveFunction.GeneralizedPerspective

Topic: quantum   Node: f39dccbc8a9a

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.GeneralizedPerspective`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The generalized perspective function `(fΔh)(A, B) = h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2)`. This definition is intended to be used when `A` is Hermitian and `h(B)` is positive/invertible.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GeneralizedPerspectiveFunction in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The generalized perspective function `(fΔh)(A, B) = h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2)`. This definition is intended to be used when `A` is Hermitian and `h(B)` is positive/invertible. -/
noncomputable def GeneralizedPerspectiveFunction.GeneralizedPerspective (f h : ℝ → ℝ) (A B : L ℋ) : L ℋ :=
  hSqrt h B * cfcR f (hInvSqrt h B * A * hInvSqrt h B) * hSqrt h B
