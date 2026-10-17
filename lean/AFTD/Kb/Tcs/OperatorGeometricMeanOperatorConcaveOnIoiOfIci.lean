import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremOperatorConcaveOn
import AFTD.Kb.Tcs.LownerHeinzTheoremL
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
# OperatorGeometricMean.operatorConcaveOn_Ioi_of_Ici

Topic: quantum   Node: 48c6707183a7

Provenance: formalization of a published result. Source: QuantumInfo, `OperatorGeometricMean.operatorConcaveOn_Ioi_of_Ici`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/OperatorGeometricMean.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

OperatorGeometricMean.operatorConcaveOn_Ioi_of_Ici
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit [Nontrivial ℋ] in
lemma OperatorGeometricMean.operatorConcaveOn_Ioi_of_Ici {f : ℝ → ℝ}
    (h : OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f) :
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f := by
  intro A B t hA hB ht0 ht1 hAs hBs
  exact h hA hB ht0 ht1 (Set.Subset.trans hAs Set.Ioi_subset_Ici_self)
      (Set.Subset.trans hBs Set.Ioi_subset_Ici_self)
