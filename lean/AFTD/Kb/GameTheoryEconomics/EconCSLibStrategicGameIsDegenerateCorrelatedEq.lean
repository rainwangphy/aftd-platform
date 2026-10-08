import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.IsDegenerateCorrelatedEq

Topic: equilibria   Node: c73a2c27cb9a

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsDegenerateCorrelatedEq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/CorrelatedEq.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A degenerate correlated equilibrium supported on a single profile. This is the only honest correlated-equilibrium notion currently formalized in this file: the mediator recommends one fixed profile with probability 1. In that case, obedience is exactly the Nash condition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- A degenerate correlated equilibrium supported on a single profile. This is the only honest correlated-equilibrium notion currently formalized in this file: the mediator recommends one fixed profile with probability 1. In that case, obedience is exactly the Nash condition. -/
def EconCSLib.StrategicGame.IsDegenerateCorrelatedEq (G : EconCSLib.StrategicGame N U) (σ : G.Profile) : Prop :=
  IsNashEquilibrium G σ
