import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ArenaReachable

/-!
# ExtensiveGame.TreeShapedFrom

Topic: equilibria   Node: c2b5bfc5117e

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.TreeShapedFrom`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A weak tree-shapedness condition: any two paths from the root to the same state are equal as reachability proofs. This is intentionally proof-valued. Concrete finite extraction modules may replace it with a computable predecessor/history representation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- A weak tree-shapedness condition: any two paths from the root to the same state are equal as reachability proofs. This is intentionally proof-valued. Concrete finite extraction modules may replace it with a computable predecessor/history representation. -/
def ExtensiveGame.TreeShapedFrom (root : G.State) : Prop :=
  ∀ s : G.State, Subsingleton (Arena.Reachable G.toArena root s)
