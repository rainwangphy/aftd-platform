import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeEqSomeChildValue
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeValue

/-!
# GameTree.value₀_Node_eq_some_child

Topic: equilibria   Node: 20476ebf3d82

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_Node_eq_some_child`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At any decision node, the backward-induction `value₀` is realized by one of the node's children.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- At any decision node, the backward-induction `value₀` is realized by one of the node's children. -/
theorem GameTree.value₀_Node_eq_some_child (m : Fin 2) (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) :
    ∃ c ∈ h :: t, value₀ (Node m h t) = value₀ c := by
  obtain ⟨c, hmem, hvalue⟩ := value_Node_eq_some_child_value m h t
  refine ⟨c, hmem, ?_⟩
  unfold value₀
  exact congrArg (fun v : Fin 2 → ℚ => v 0) hvalue
