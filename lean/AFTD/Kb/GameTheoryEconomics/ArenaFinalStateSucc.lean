import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaFinalState

/-!
# Arena.finalState_succ

Topic: equilibria   Node: a9b1f4d5deaf

Provenance: formalization of a published result. Source: EconCSLib, `Arena.finalState_succ`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Arena.finalState_succ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A : Arena) in
theorem Arena.finalState_succ (choose : (s : A.State) → A.Action s) (s : A.State) (n : ℕ) :
    A.finalState choose s (n + 1) = A.finalState choose (A.next s (choose s)) n := rfl
