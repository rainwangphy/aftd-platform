import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremOperatorConcaveOn
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint

/-!
# LownerHeinzTheorem.OperatorConcaveOnAll

Topic: quantum   Node: 9822add90a9c

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzTheorem.OperatorConcaveOnAll`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform operator concavity on `s` over all Hilbert spaces in universe `u`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzTheorem in
universe u v in
open CFC in
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity on `s` over all Hilbert spaces in universe `u`. -/
def LownerHeinzTheorem.OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcaveOn (ℋ := K) s f
