import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameNashMapAux
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunction
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameOneLeSumG
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameGFunctionNonneg
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.nash_map_cert

Topic: equilibria   Node: a8b3760e3baa

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.nash_map_cert`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normalized augmented weights form a valid probability distribution on `G.strategy i`.
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
/-- The normalized augmented weights form a valid probability distribution on `G.strategy i`. -/
lemma EconCSLib.StrategicGame.nash_map_cert (σ : MixedS G) (i : N) :
    nash_map_aux G σ i ∈ stdSimplex ℝ (G.strategy i) := by
  have hd : 0 < ∑ b : G.strategy i, g_function G i σ b :=
    lt_of_lt_of_le one_pos (one_le_sum_g G i σ)
  constructor
  · intro a
    exact div_nonneg (g_function_nonneg G i σ a) (le_of_lt hd)
  · simp only [nash_map_aux, ← Finset.sum_div]
    exact div_self (ne_of_gt hd)
