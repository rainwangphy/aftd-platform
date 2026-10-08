import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# Arena.Reachable.step'

Topic: equilibria   Node: 82dd9dacdaf1

Provenance: formalization of a published result. Source: EconCSLib, `Arena.Reachable.step'`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Taking one legal action extends a reachable path.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Taking one legal action extends a reachable path. -/
theorem Arena.Reachable.step' {A : Arena} {s t : A.State}
    (h : A.Reachable s t) (action : A.Action t) :
    A.Reachable s (A.next t action) :=
  h.trans (.step action (.refl _))
