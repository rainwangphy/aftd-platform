import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ArenaReachableStep'

/-!
# ExtensiveGame.reachableSubgameAt

Topic: equilibria   Node: 8929877889bd

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.reachableSubgameAt`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Subgame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subgame whose state space is restricted to states reachable from `root`. The older `subgameAt` view changes only the initial state. This subtype version is useful when a proof needs to express that deviations are local to the subtree below `root`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- The subgame whose state space is restricted to states reachable from `root`. The older `subgameAt` view changes only the initial state. This subtype version is useful when a proof needs to express that deviations are local to the subtree below `root`. -/
def ExtensiveGame.reachableSubgameAt (G : ExtensiveGame iota U) (root : G.State) :
    ExtensiveGame iota U where
  State := {s : G.State // Arena.Reachable G.toArena root s}
  Action := fun s => G.Action s.1
  next := fun s a => ⟨G.next s.1 a, s.2.step' a⟩
  init := ⟨root, Arena.Reachable.refl _⟩
  mover := fun s => G.mover s.1
  payoff := fun s i => G.payoff s.1 i
