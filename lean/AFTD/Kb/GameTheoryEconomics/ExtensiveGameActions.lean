import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame

/-!
# ExtensiveGame.actions

Topic: equilibria   Node: 15743590bd4c

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.actions`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Available actions at a state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- Available actions at a state. -/
abbrev ExtensiveGame.actions (G : ExtensiveGame N U) (s : G.State) := G.Action s
