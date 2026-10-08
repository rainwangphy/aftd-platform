import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtreeHead
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtreeTailMem

/-!
# GameTree.Subtree.child_mem

Topic: equilibria   Node: 5492935c25bc

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Subtree.child_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any child (head or tail) is a subtree.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- Any child (head or tail) is a subtree. -/
theorem GameTree.Subtree.child_mem (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ h :: t) : Subtree c (Node m h t) := by
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact Subtree.head m c t
  · exact Subtree.tail_mem m h t hmem'
