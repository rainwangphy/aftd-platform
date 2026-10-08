import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeStrongInduction
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeEqSomeChildValue
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSumChildMem
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSumHead

/-!
# GameTree.value_zero_sum

Topic: equilibria   Node: 2bb7b0ad4a77

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value_zero_sum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Backward induction preserves the zero-sum invariant: if every terminal payoff vector is zero-sum, then the selected backward-induction value vector is zero-sum as well.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Backward induction preserves the zero-sum invariant: if every terminal payoff vector is zero-sum, then the selected backward-induction value vector is zero-sum as well. -/
theorem GameTree.value_zero_sum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (value g) 0 + (value g) 1 = 0 := by
  revert hzs
  induction g using GameTree.strong_induction with
  | base p =>
      intro hzs
      simpa [IsZeroSum] using hzs
  | step m h t ih =>
      intro hzs
      obtain ⟨c, hmem, hvalue⟩ := value_Node_eq_some_child_value m h t
      rw [hvalue]
      exact ih c hmem (IsZeroSum.child_mem hzs hmem)
