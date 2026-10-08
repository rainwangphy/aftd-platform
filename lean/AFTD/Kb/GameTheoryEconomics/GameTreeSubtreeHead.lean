import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree

/-!
# GameTree.Subtree.head

Topic: equilibria   Node: e7bc5cf4dac7

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Subtree.head`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The head of a `Node` is a subtree of the node.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- The head of a `Node` is a subtree of the node. -/
theorem GameTree.Subtree.head (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    Subtree h (Node m h t) :=
  Subtree.inHead h m h t (Subtree.refl h)
