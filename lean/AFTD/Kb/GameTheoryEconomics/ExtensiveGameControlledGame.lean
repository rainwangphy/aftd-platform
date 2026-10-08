import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ControlledGame

/-!
# ExtensiveGame.controlledGame

Topic: equilibria   Node: 1259c5219c22

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.controlledGame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Forget only the state-payoff interpretation. This is a lossless projection for dynamics, the initial root, and mover data. It is the canonical migration path from payoff-aware APIs to structural or logical-game APIs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- Forget only the state-payoff interpretation. This is a lossless projection for dynamics, the initial root, and mover data. It is the canonical migration path from payoff-aware APIs to structural or logical-game APIs. -/
abbrev ExtensiveGame.controlledGame (G : ExtensiveGame N U) : ControlledGame N :=
  G.toControlledGame
