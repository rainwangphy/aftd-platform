import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityInnerHsumInclHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjAdjoint

/-!
# JensenOperatorInequality.hsumIncl_proj_sum

Topic: quantum   Node: 37472553adee

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumIncl_proj_sum`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.hsumIncl_proj_sum
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem JensenOperatorInequality.hsumIncl_proj_sum (z : HSum ℋ) :
    hsumIncl ℋ 0 (hsumProj ℋ 0 z) + hsumIncl ℋ 1 (hsumProj ℋ 1 z) = z := by
  ext i
  fin_cases i <;> simp [hsumProj, hsumIncl, hsumEquiv]
