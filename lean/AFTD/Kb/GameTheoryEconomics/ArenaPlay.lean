import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# Arena.play

Topic: equilibria   Node: dd18f28bd45f

Provenance: formalization of a published result. Source: EconCSLib, `Arena.play`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Play the game for at most `fuel` steps, using `choose` to pick actions. Returns the sequence of states visited.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A : Arena) in
/-- Play the game for at most `fuel` steps, using `choose` to pick actions. Returns the sequence of states visited. -/
def Arena.play (choose : (s : A.State) → A.Action s)
    (start : A.State) : (fuel : ℕ) → List A.State
  | 0 => [start]
  | n + 1 => start :: play choose (A.next start (choose start)) n
