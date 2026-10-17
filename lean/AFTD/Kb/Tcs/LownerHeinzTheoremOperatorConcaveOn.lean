import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreOperatorConcaveOn
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# LownerHeinzTheorem.OperatorConcaveOn

Topic: quantum   Node: 7e7b8f3f59d2

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzTheorem.OperatorConcaveOn`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed-space operator concavity on `s` for the Hilbert space `ℋ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzTheorem in
universe u v in
open CFC in
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- Fixed-space operator concavity on `s` for the Hilbert space `ℋ`. -/
def LownerHeinzTheorem.OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOn (𝓐 := L ℋ) s f
