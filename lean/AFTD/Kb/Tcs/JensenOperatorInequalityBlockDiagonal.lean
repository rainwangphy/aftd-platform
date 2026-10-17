import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjHsumInclApply
import AFTD.Kb.Tcs.JensenOperatorInequalityInnerHsumInclHsumIncl
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumInclProjSum
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequality.blockDiagonal

Topic: quantum   Node: 3fd62124285f

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.blockDiagonal`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The block diagonal operator `diag(A, B)` on the two-fold Hilbert sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The block diagonal operator `diag(A, B)` on the two-fold Hilbert sum. -/
noncomputable def JensenOperatorInequality.blockDiagonal (A B : L ℋ) : L (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L B ∘L hsumProj ℋ 1
