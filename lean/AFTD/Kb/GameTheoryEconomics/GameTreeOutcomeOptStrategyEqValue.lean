import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeStrongInduction
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeValueOptStrategyEq
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.outcome_optStrategy_eq_value

Topic: equilibria   Node: 77cceb1e2d2e

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.outcome_optStrategy_eq_value`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Key lemma**: the outcome of the backward-induction strategy equals the backward-induction value vector at every game tree. This is the bridge between `value` (defined via argmax) and `outcome` (defined via tree traversal).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- **Key lemma**: the outcome of the backward-induction strategy equals the backward-induction value vector at every game tree. This is the bridge between `value` (defined via argmax) and `outcome` (defined via tree traversal). -/
theorem GameTree.outcome_optStrategy_eq_value [DecidableLE U] (g : GameTree N U) :
    outcome (optStrategy : Strategy N U) g = value g := by
  induction g using GameTree.strong_induction with
  | base p => simp [outcome_Leaf, value_Leaf]
  | step m h t ih =>
      -- outcome optStrategy (Node m h t) = outcome optStrategy (optStrategy m h t).val
      -- By IH on the chosen child: = value (optStrategy m h t).val
      -- By value_optStrategy_eq:   = value (Node m h t)
      rw [outcome_Node]
      have hmem : (optStrategy m h t).val ∈ h :: t := (optStrategy m h t).property
      rw [ih _ hmem]
      exact value_optStrategy_eq m h t
