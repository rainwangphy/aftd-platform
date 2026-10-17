import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreOperatorConcave
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# LownerHeinzTheorem.OperatorConcave

Topic: quantum   Node: e3321e1058ce

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzTheorem.OperatorConcave`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed-space operator concavity on the Hilbert space `ℋ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzTheorem in
universe u v in
open CFC in
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- Fixed-space operator concavity on the Hilbert space `ℋ`. -/
def LownerHeinzTheorem.OperatorConcave (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcave (𝓐 := L ℋ) f
