import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityInnerHsumInclHsumIncl

/-!
# JensenOperatorInequality.hsumProj_adjoint

Topic: quantum   Node: d370f55e21dd

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumProj_adjoint`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.hsumProj_adjoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
@[simp] theorem JensenOperatorInequality.hsumProj_adjoint (i : Fin 2) :
    (hsumProj ℋ i).adjoint = hsumIncl ℋ i := by
  calc
    (hsumProj ℋ i).adjoint = ((hsumIncl ℋ i).adjoint).adjoint := by
      rw [hsumIncl_adjoint (ℋ := ℋ) i]
    _ = hsumIncl ℋ i := ContinuousLinearMap.adjoint_adjoint _
