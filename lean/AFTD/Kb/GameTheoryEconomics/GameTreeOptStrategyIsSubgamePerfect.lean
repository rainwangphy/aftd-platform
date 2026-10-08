import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeOptStrategyEqValue
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeStrongInduction
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeValueOptStrategyEq
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeGe
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.optStrategy_isSubgamePerfect

Topic: equilibria   Node: 4ade2c3bac37

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.optStrategy_isSubgamePerfect`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Optimality of `optStrategy`**: for every subtree `g`, every player `i`, and every `i`-variant deviation `σ'`, the deviating outcome is no better than `optStrategy`'s outcome at coordinate `i`. This is the SPE property spelled out before bundling into existence form.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- **Optimality of `optStrategy`**: for every subtree `g`, every player `i`, and every `i`-variant deviation `σ'`, the deviating outcome is no better than `optStrategy`'s outcome at coordinate `i`. This is the SPE property spelled out before bundling into existence form. -/
theorem GameTree.optStrategy_isSubgamePerfect [DecidableLE U] :
    IsSubgamePerfect (optStrategy : Strategy N U) := by
  intro g i σ' hiv
  induction g using GameTree.strong_induction with
  | base p =>
      -- Both outcomes equal `p`; `≤` holds by reflexivity.
      simp [outcome_Leaf]
  | step m h t ih =>
      -- Two subcases depending on whether the mover is the deviating player.
      rw [outcome_Node, outcome_Node]
      by_cases hmi : m = i
      · -- Mover = deviating player. σ' can pick any child c'; optStrategy picks argmax.
        -- Use IH on c' to compare σ' vs optStrategy there, then value_Node_ge.
        have hmem' : (σ' m h t).val ∈ h :: t := (σ' m h t).property
        -- IH on c' gives: outcome σ' c' i ≤ outcome optStrategy c' i
        have h_ih := ih _ hmem'
        -- Bridge: outcome optStrategy c' = value c'
        rw [outcome_optStrategy_eq_value] at h_ih
        -- value c' i ≤ value (Node m h t) i by value_Node_ge
        have h_max : (value (σ' m h t).val) i ≤ (value (Node m h t)) i := by
          subst hmi
          exact value_Node_ge m h t _ hmem'
        -- Right side: outcome optStrategy (optStrategy m h t).val i = value (Node m h t) i
        have h_rhs : outcome optStrategy (optStrategy m h t).val i =
                       (value (Node m h t)) i := by
          rw [outcome_optStrategy_eq_value]
          exact congrArg (· i) (value_optStrategy_eq m h t)
        calc outcome σ' (σ' m h t).val i
            ≤ (value (σ' m h t).val) i := h_ih
          _ ≤ (value (Node m h t)) i := h_max
          _ = outcome optStrategy (optStrategy m h t).val i := h_rhs.symm
      · -- Mover ≠ deviating player: σ' and optStrategy pick the same child.
        have hsame : σ' m h t = optStrategy m h t := (hiv m h t hmi).symm
        rw [hsame]
        -- Apply IH on the shared child
        have hmem : (optStrategy m h t).val ∈ h :: t := (optStrategy m h t).property
        exact ih _ hmem
