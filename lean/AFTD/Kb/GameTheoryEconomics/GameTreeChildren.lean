import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.children

Topic: equilibria   Node: bbc7ccd0436e

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.children`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The full child list at a `Node`, as a guaranteed non-empty list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- The full child list at a `Node`, as a guaranteed non-empty list. -/
@[simp]
def GameTree.children : GameTree N U → List (GameTree N U)
  | Leaf _ => []
  | Node _ h t => h :: t
