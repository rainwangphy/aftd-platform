import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL

/-!
# JensenOperatorInequality.spectrum_Ici_of_nonneg

Topic: quantum   Node: 5ee10a648c3c

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.spectrum_Ici_of_nonneg`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.spectrum_Ici_of_nonneg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.spectrum_Ici_of_nonneg {A : L ℋ} (hA0 : (0 : L ℋ) ≤ A) :
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
  exact
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A
      (ha := IsSelfAdjoint.of_nonneg hA0)).1 hA0
