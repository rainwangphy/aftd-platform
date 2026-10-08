import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaIsTerminal
import AFTD.Kb.GameTheoryEconomics.ArenaIsDecision

/-!
# Arena.isTerminal_iff_not_isDecision

Topic: equilibria   Node: def44c46828f

Provenance: formalization of a published result. Source: EconCSLib, `Arena.isTerminal_iff_not_isDecision`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Terminal and decision states are complementary.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (A : Arena) in
/-- Terminal and decision states are complementary. -/
theorem Arena.isTerminal_iff_not_isDecision (s : A.State) :
    A.IsTerminal s ↔ ¬ A.IsDecision s := by
  simp [IsTerminal, IsDecision, isEmpty_iff, not_nonempty_iff]
