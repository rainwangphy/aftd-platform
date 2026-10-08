import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.PlayerStrategy

Topic: equilibria   Node: b91e191ef872

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.PlayerStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeStrategicForm.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A single player's pure strategy in the normal form of a `GameTree`: a complete contingent plan choosing a child at every possible node.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
variable [DecidableEq N] in
/-- A single player's pure strategy in the normal form of a `GameTree`: a complete contingent plan choosing a child at every possible node. -/
def GameTree.PlayerStrategy (N U : Type*) : Type _ :=
  (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
    { c : GameTree N U // c ∈ h :: t }
