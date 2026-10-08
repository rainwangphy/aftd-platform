import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ExtensiveGame.ActionListComplete

Topic: equilibria   Node: f84ede9dff6f

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ActionListComplete`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonempty action list `head :: tail` contains every available action at state `s`. The list is an explicit finite enumeration supplied by the concrete game.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- A nonempty action list `head :: tail` contains every available action at state `s`. The list is an explicit finite enumeration supplied by the concrete game. -/
def ExtensiveGame.ActionListComplete (s : G.State) (head : G.Action s) (tail : List (G.Action s)) :
    Prop :=
  ∀ a : G.Action s, a ∈ head :: tail

/- Relational extraction of an Arena-style no-chance extensive game state to a
    finite `GameTree`.

The relation is intentionally assumption-explicit: each decision node supplies a
complete nonempty action enumeration, a player owner, and extracted child trees
for exactly that action list. -/
