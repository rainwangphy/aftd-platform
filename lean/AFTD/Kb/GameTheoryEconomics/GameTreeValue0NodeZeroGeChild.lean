import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeGe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeValue

/-!
# GameTree.value₀_Node_zero_ge_child

Topic: equilibria   Node: 69a7aad42bfa

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_Node_zero_ge_child`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At a player-0 node, `value₀` is at least the `value₀` of every child.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- At a player-0 node, `value₀` is at least the `value₀` of every child. -/
theorem GameTree.value₀_Node_zero_ge_child (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) (c : GameTree (Fin 2) ℚ)
    (hmem : c ∈ h :: t) :
    value₀ c ≤ value₀ (Node (0 : Fin 2) h t) := by
  unfold value₀
  exact value_Node_ge (0 : Fin 2) h t c hmem
