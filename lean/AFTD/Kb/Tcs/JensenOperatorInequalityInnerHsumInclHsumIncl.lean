import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply

/-!
# JensenOperatorInequality.inner_hsumIncl_hsumIncl

Topic: quantum   Node: baa92d0245d2

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.inner_hsumIncl_hsumIncl`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.inner_hsumIncl_hsumIncl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem JensenOperatorInequality.inner_hsumIncl_hsumIncl (i j : Fin 2) (x y : ℋ) :
    inner ℂ (hsumIncl ℋ i x) (hsumIncl ℋ j y) = if i = j then inner ℂ x y else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumIncl, hsumEquiv, PiLp.inner_apply]
