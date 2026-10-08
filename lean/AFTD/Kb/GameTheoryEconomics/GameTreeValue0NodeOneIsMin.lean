import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0NodeEqSomeChild
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0NodeOneLeChild
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
# GameTree.value₀_Node_one_isMin

Topic: equilibria   Node: b828d021c787

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_Node_one_isMin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At a zero-sum player-1 node, some child realizes the node's `value₀`, and that value is no greater than every child's `value₀`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- At a zero-sum player-1 node, some child realizes the node's `value₀`, and that value is no greater than every child's `value₀`. -/
theorem GameTree.value₀_Node_one_isMin (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) (hzs : IsZeroSum (Node (1 : Fin 2) h t)) :
    ∃ c ∈ h :: t,
      value₀ (Node (1 : Fin 2) h t) = value₀ c ∧
      ∀ d ∈ h :: t, value₀ c ≤ value₀ d := by
  obtain ⟨c, hmem, hvalue⟩ := value₀_Node_eq_some_child (1 : Fin 2) h t
  refine ⟨c, hmem, hvalue, ?_⟩
  intro d hdmem
  rw [← hvalue]
  exact value₀_Node_one_le_child h t hzs d hdmem
