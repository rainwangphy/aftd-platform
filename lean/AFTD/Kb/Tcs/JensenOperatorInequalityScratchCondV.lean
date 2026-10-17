import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityScratchCondIV
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
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
# JensenOperatorInequalityScratch.CondV

Topic: quantum   Node: d9993c771f1a

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequalityScratch.CondV`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIVtoV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Local copy of condition (v) for fast iteration on `(iv) → (v)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequalityScratch in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- Local copy of condition (v) for fast iteration on `(iv) → (v)`. -/
def JensenOperatorInequalityScratch.CondV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B X Y : L ℋ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → spectrum ℝ B ⊆ Set.Ici (0 : ℝ) →
    star X * X + star Y * Y ≤ (1 : L ℋ) →
    cfcR (ℋ := ℋ) f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y
