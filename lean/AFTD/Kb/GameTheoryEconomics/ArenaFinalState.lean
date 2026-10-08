import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaPlay

/-!
# Arena.finalState

Topic: equilibria   Node: b44f305c9091

Provenance: formalization of a published result. Source: EconCSLib, `Arena.finalState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The final state after at most `fuel` steps.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A : Arena) in
/-- The final state after at most `fuel` steps. -/
def Arena.finalState (choose : (s : A.State) → A.Action s)
    (start : A.State) : (fuel : ℕ) → A.State
  | 0 => start
  | n + 1 => finalState choose (A.next start (choose start)) n
