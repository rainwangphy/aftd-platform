import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren

/-!
# GameTree.children_node_ne_nil

Topic: equilibria   Node: 89720bdbf497

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.children_node_ne_nil`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Children of a `Node` are never empty.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- Children of a `Node` are never empty. -/
theorem GameTree.children_node_ne_nil (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    children (Node m h t) ≠ [] := by
  simp [children]
