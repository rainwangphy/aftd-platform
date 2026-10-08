import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsReachable
import AFTD.Kb.GameTheoryEconomics.ArenaReachableStep'

/-!
# ExtensiveGame.IsReachable.next

Topic: equilibria   Node: d54d38bb68c5

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.IsReachable.next`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Execution/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `s` is reachable and we take action `a`, then `next s a` is reachable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- If `s` is reachable and we take action `a`, then `next s a` is reachable. -/
theorem ExtensiveGame.IsReachable.next {G : ExtensiveGame N U} {s : G.State}
    (h : G.IsReachable s) (a : G.Action s) :
    G.IsReachable (G.next s a) :=
  h.step' a
