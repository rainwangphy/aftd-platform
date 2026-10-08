import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaIsTerminal

/-!
# ControlledGame.isTerminal

Topic: equilibria   Node: 497d8e259773

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame.isTerminal`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is terminal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- A state is terminal. -/
abbrev ControlledGame.isTerminal (G : ControlledGame N) (s : G.State) :=
  G.toArena.IsTerminal s
