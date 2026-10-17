import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityInnerHsumInclHsumIncl

/-!
# JensenOperatorInequality.hsumIncl_adjoint

Topic: quantum   Node: f08441b4ab38

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumIncl_adjoint`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.hsumIncl_adjoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
@[simp] theorem JensenOperatorInequality.hsumIncl_adjoint (i : Fin 2) :
    (hsumIncl ℋ i).adjoint = hsumProj ℋ i := by
  fin_cases i
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
