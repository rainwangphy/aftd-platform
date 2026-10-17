import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionPdSet
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionPsdSet
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
# OperatorGeometricMean.pdSet_subset_psdSet

Topic: quantum   Node: 4ab572ce46fd

Provenance: formalization of a published result. Source: QuantumInfo, `OperatorGeometricMean.pdSet_subset_psdSet`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/OperatorGeometricMean.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

OperatorGeometricMean.pdSet_subset_psdSet
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
open GeneralizedPerspectiveFunction in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
lemma OperatorGeometricMean.pdSet_subset_psdSet : pdSet (ℋ := ℋ) ⊆ psdSet (ℋ := ℋ) := by
  intro A hA
  rcases hA with ⟨hA_sa, hA_spec⟩
  exact ⟨hA_sa, Set.Subset.trans hA_spec Set.Ioi_subset_Ici_self⟩
