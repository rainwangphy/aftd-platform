import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree

/-!
# StochasticGameTree.ofGameTree

Topic: equilibria   Node: 7e64a2559e6b

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.ofGameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embed an ordinary no-chance `GameTree` into the stochastic tree layer.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} in
/-- Embed an ordinary no-chance `GameTree` into the stochastic tree layer. -/
def StochasticGameTree.ofGameTree : GameTree N ℚ → StochasticGameTree N
  | GameTree.Leaf p => StochasticGameTree.Leaf p
  | GameTree.Node m h t => StochasticGameTree.Player m (ofGameTree h) (t.map ofGameTree)
