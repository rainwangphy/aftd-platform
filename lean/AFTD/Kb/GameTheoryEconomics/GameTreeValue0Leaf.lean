import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValue0
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeValue

/-!
# GameTree.value₀_Leaf

Topic: equilibria   Node: 652cde78f7d3

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value₀_Leaf`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At a zero-sum leaf, `value₀` equals player 0's payoff and `-value₀` equals player 1's.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- At a zero-sum leaf, `value₀` equals player 0's payoff and `-value₀` equals player 1's. -/
theorem GameTree.value₀_Leaf (p : Fin 2 → ℚ) (_h : IsZeroSum (Leaf p)) :
    value₀ (Leaf p) = p 0 := by
  unfold value₀
  simp
