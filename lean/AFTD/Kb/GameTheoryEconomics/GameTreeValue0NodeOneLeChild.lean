import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeGe
import AFTD.Kb.GameTheoryEconomics.GameTreeValueOneEqNegValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSumChildMem
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeValue

/-!
# GameTree.value₀_Node_one_le_child

Topic: equilibria   Node: 30fb7f9673a8

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_Node_one_le_child`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At a zero-sum player-1 node, `value₀` is no greater than the `value₀` of every child. Equivalently, player 1's local maximization of their own value is player 0's local minimization.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- At a zero-sum player-1 node, `value₀` is no greater than the `value₀` of every child. Equivalently, player 1's local maximization of their own value is player 0's local minimization. -/
theorem GameTree.value₀_Node_one_le_child (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) (hzs : IsZeroSum (Node (1 : Fin 2) h t))
    (c : GameTree (Fin 2) ℚ) (hmem : c ∈ h :: t) :
    value₀ (Node (1 : Fin 2) h t) ≤ value₀ c := by
  have hge : (value c) 1 ≤ (value (Node (1 : Fin 2) h t)) 1 :=
    value_Node_ge (1 : Fin 2) h t c hmem
  rw [value_one_eq_neg_value₀ c (IsZeroSum.child_mem hzs hmem),
    value_one_eq_neg_value₀ (Node (1 : Fin 2) h t) hzs] at hge
  exact neg_le_neg_iff.mp hge
