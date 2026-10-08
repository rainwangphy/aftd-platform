import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunction
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameSigmaLeGFunction
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.one_le_sum_g

Topic: equilibria   Node: f74edfa3a6de

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.one_le_sum_g`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The sum of augmented weights is at least 1.
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
/-- The sum of augmented weights is at least 1. -/
lemma EconCSLib.StrategicGame.one_le_sum_g (i : N) (σ : MixedS G) :
    1 ≤ ∑ a : G.strategy i, g_function G i σ a := by
  calc 1 = ∑ a : G.strategy i, (σ i).val a := (σ i).property.2.symm
    _ ≤ ∑ a : G.strategy i, g_function G i σ a :=
        Finset.sum_le_sum fun a _ => sigma_le_g_function G i σ a
