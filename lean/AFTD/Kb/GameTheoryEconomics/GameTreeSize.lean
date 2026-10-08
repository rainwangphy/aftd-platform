import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.size

Topic: equilibria   Node: 6442cc20e635

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.size`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Structural size, used for well-founded recursion.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- Structural size, used for well-founded recursion. -/
def GameTree.size : GameTree N U → ℕ
  | Leaf _ => 1
  | Node _ h t => 1 + h.size + (t.map size).sum
