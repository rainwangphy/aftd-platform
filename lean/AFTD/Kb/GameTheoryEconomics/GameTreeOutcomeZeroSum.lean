import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeStrongInduction
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSumChildMem
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.Tcs.G

/-!
# GameTree.outcome_zero_sum

Topic: equilibria   Node: 3f15a7bb64f0

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.outcome_zero_sum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a zero-sum tree, the terminal outcome of **any** strategy is zero-sum: following any strategy ends at some leaf, and every leaf of a zero-sum tree is zero-sum. This is the strategy-level analogue of `value_zero_sum`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- In a zero-sum tree, the terminal outcome of **any** strategy is zero-sum: following any strategy ends at some leaf, and every leaf of a zero-sum tree is zero-sum. This is the strategy-level analogue of `value_zero_sum`. -/
theorem GameTree.outcome_zero_sum (σ : Strategy (Fin 2) ℚ) (g : GameTree (Fin 2) ℚ)
    (hzs : IsZeroSum g) :
    outcome σ g 0 + outcome σ g 1 = 0 := by
  revert hzs
  induction g using GameTree.strong_induction with
  | base p =>
      intro hzs
      simpa [outcome_Leaf, IsZeroSum] using hzs
  | step m h t ih =>
      intro hzs
      rw [outcome_Node]
      have hmem : (σ m h t).val ∈ h :: t := (σ m h t).property
      exact ih _ hmem (IsZeroSum.child_mem hzs hmem)
