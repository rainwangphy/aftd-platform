import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ArenaPlay

/-!
# ExtensiveGame.play

Topic: equilibria   Node: ac30199d20b5

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.play`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Play the game from `init` for at most `fuel` steps. Requires a default action chooser for all states (including chance).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} (G : ExtensiveGame N U) in
/-- Play the game from `init` for at most `fuel` steps. Requires a default action chooser for all states (including chance). -/
def ExtensiveGame.play (choose : (s : G.State) → G.Action s) (fuel : ℕ) : List G.State :=
  G.toArena.play choose G.init fuel
