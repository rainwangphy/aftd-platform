import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsDegenerateCorrelatedEq
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# EconCSLib.StrategicGame.nash_iff_degenerate_ce

Topic: equilibria   Node: fbfe727c0cc8

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.nash_iff_degenerate_ce`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/CorrelatedEq.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A profile is a "degenerate" correlated equilibrium (point mass on one profile) if and only if it is a Nash equilibrium.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- A profile is a "degenerate" correlated equilibrium (point mass on one profile) if and only if it is a Nash equilibrium. -/
theorem EconCSLib.StrategicGame.nash_iff_degenerate_ce (G : EconCSLib.StrategicGame N U) (σ : G.Profile) :
    IsNashEquilibrium G σ ↔ IsDegenerateCorrelatedEq G σ := by
  exact Iff.rfl
