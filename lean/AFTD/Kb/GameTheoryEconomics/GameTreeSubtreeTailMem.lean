import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree

/-!
# GameTree.Subtree.tail_mem

Topic: equilibria   Node: bbcaaf5de0f5

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Subtree.tail_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any tail member of a `Node` is a subtree of the node.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- Any tail member of a `Node` is a subtree of the node. -/
theorem GameTree.Subtree.tail_mem (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ t) : Subtree c (Node m h t) :=
  Subtree.inTail c m h t hmem (Subtree.refl c)
