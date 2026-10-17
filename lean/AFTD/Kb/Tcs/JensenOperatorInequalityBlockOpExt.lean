import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclProjSum
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequality.blockOp_ext

Topic: quantum   Node: 2d6e42f4386e

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.blockOp_ext`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.blockOp_ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem JensenOperatorInequality.blockOp_ext {T S : L (HSum ℋ)}
    (h0 : ∀ z : HSum ℋ, hsumProj ℋ 0 (T z) = hsumProj ℋ 0 (S z))
    (h1 : ∀ z : HSum ℋ, hsumProj ℋ 1 (T z) = hsumProj ℋ 1 (S z)) :
    T = S := by
  ext z i
  fin_cases i
  · exact h0 z
  · exact h1 z
