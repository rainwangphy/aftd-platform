import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaFinalState

/-!
# Arena.finalState_zero

Topic: equilibria   Node: 1637ae123b24

Provenance: formalization of a published result. Source: EconCSLib, `Arena.finalState_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Play.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Arena.finalState_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A : Arena) in
theorem Arena.finalState_zero (choose : (s : A.State) → A.Action s) (s : A.State) :
    A.finalState choose s 0 = s := rfl
