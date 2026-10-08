import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# GameTree.Strategy

Topic: equilibria   Node: c118886d0e9a

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Strategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure strategy for the entire game tree: at every possible node context `(mover, head, tail)`, specify one child (bundled with its membership proof). Note: a single `Strategy` covers all players. Player-`i` "strategies" are conceptualized as the restriction to nodes where `mover = i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] in
/-- A pure strategy for the entire game tree: at every possible node context `(mover, head, tail)`, specify one child (bundled with its membership proof). Note: a single `Strategy` covers all players. Player-`i` "strategies" are conceptualized as the restriction to nodes where `mover = i`. -/
def GameTree.Strategy (N U : Type*) : Type _ :=
  (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
    { c : GameTree N U // c ∈ h :: t }
