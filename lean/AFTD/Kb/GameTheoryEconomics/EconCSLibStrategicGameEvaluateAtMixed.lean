import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.evaluate_at_mixed

Topic: equilibria   Node: 8dc249ea71f8

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.evaluate_at_mixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected payoff of player `i` under mixed profile `σ`. Sums over all pure profiles, weighting by the product of each player's probability.
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
/-- Expected payoff of player `i` under mixed profile `σ`. Sums over all pure profiles, weighting by the product of each player's probability. -/
noncomputable def EconCSLib.StrategicGame.evaluate_at_mixed (i : N) (σ : MixedS G) : ℝ :=
  ∑ s : G.Profile, (∏ j : N, (σ j).val (s j)) * G.payoff s i
