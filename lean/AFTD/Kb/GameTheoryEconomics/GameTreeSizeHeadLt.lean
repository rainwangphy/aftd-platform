import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSize

/-!
# GameTree.size_head_lt

Topic: equilibria   Node: 74a64a25b8e6

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.size_head_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The head of a `Node`'s children is structurally smaller.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- The head of a `Node`'s children is structurally smaller. -/
theorem GameTree.size_head_lt (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    h.size < (Node m h t).size := by
  simp [size]
  have : 0 ≤ (t.map size).sum := Nat.zero_le _
  omega
