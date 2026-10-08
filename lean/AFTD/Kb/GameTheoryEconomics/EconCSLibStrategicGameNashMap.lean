import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameNashMapAux
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameNashMapCert
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.nash_map

Topic: equilibria   Node: 428b09cc68f0

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.nash_map`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Nash best-response map: sends a mixed profile `σ` to the profile where each player `i` plays proportional to `g_function i σ`. A fixed point of this map is a mixed Nash equilibrium.
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
/-- The Nash best-response map: sends a mixed profile `σ` to the profile where each player `i` plays proportional to `g_function i σ`. A fixed point of this map is a mixed Nash equilibrium. -/
noncomputable def EconCSLib.StrategicGame.nash_map (σ : MixedS G) : MixedS G :=
  fun i => ⟨nash_map_aux G σ i, nash_map_cert G σ i⟩
