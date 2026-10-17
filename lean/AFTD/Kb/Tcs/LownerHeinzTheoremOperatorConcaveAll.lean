import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremOperatorConcave
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# LownerHeinzTheorem.OperatorConcaveAll

Topic: quantum   Node: ed220518869a

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzTheorem.OperatorConcaveAll`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform operator concavity over all Hilbert spaces in universe `u`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzTheorem in
universe u v in
open CFC in
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity over all Hilbert spaces in universe `u`. -/
def LownerHeinzTheorem.OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcave (ℋ := K) f
