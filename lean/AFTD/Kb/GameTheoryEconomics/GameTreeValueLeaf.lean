import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren

/-!
# GameTree.value_Leaf

Topic: equilibria   Node: 0080f40a7d68

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value_Leaf`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GameTree.value_Leaf
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] [DecidableLE U] in
@[simp]
theorem GameTree.value_Leaf (p : N → U) : value (Leaf p : GameTree N U) = p := rfl
