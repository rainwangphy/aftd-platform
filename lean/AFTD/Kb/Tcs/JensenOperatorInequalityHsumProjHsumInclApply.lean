import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv

/-!
# JensenOperatorInequality.hsumProj_hsumIncl_apply

Topic: quantum   Node: 64f96c19c781

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumProj_hsumIncl_apply`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.hsumProj_hsumIncl_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem JensenOperatorInequality.hsumProj_hsumIncl_apply (i j : Fin 2) (x : ℋ) :
    hsumProj ℋ i (hsumIncl ℋ j x) = if i = j then x else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumProj, hsumIncl, hsumEquiv]
