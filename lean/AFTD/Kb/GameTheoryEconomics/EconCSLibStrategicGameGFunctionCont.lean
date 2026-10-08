import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunction
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixed
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixedUpdateCont
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixedCont
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.g_function_cont

Topic: equilibria   Node: c6a9c3b416d7

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.g_function_cont`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`g_function G i (· ) a` is continuous in the mixed profile (fixed `i`, `a`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Function in
set_option linter.unusedSectionVars false in
variable {N : Type*} in
variable (G : EconCSLib.StrategicGame N ℝ) in
variable [Fintype N] [DecidableEq N] in
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)] in
variable [∀ i, Inhabited (G.strategy i)] in
/-- `g_function G i (· ) a` is continuous in the mixed profile (fixed `i`, `a`). -/
lemma EconCSLib.StrategicGame.g_function_cont (i : N) (a : G.strategy i) :
    Continuous (fun σ : MixedS G => g_function G i σ a) := by
  unfold g_function
  apply Continuous.add
  · have h1 : Continuous (fun σ : MixedS G => σ i) := continuous_apply i
    have h2 : Continuous (fun x : stdSimplex ℝ (G.strategy i) => x.val a) :=
      (continuous_apply a).comp continuous_subtype_val
    exact h2.comp h1
  · apply Continuous.max continuous_const
    exact (evaluate_at_mixed_update_cont G i a).sub (evaluate_at_mixed_cont G i)
