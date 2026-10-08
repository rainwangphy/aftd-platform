import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixed
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.g_function

Topic: equilibria   Node: c01ef0db5c31

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.g_function`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Augmented weight for pure strategy `a` of player `i` at mixed profile `σ`: the original probability `σ_i(a)` plus the positive part of the gain from deviating to pure strategy `a`.
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
/-- Augmented weight for pure strategy `a` of player `i` at mixed profile `σ`: the original probability `σ_i(a)` plus the positive part of the gain from deviating to pure strategy `a`. -/
noncomputable def EconCSLib.StrategicGame.g_function (i : N) (σ : MixedS G) (a : G.strategy i) : ℝ :=
  (σ i).val a +
    max 0 (evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) -
           evaluate_at_mixed G i σ)
