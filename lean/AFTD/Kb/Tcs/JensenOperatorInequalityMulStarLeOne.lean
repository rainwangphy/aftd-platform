import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# JensenOperatorInequality.mul_star_le_one

Topic: quantum   Node: 8ab9b58222eb

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.mul_star_le_one`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.mul_star_le_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.mul_star_le_one [Nontrivial ℋ] (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    (X * star X : L ℋ) ≤ 1 := by
  have h1 : X * star X ≤ algebraMap ℝ (L ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := star X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

-- `simp` and normalization over block expressions are expensive here.
