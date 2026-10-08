import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeEqSomeChildValue
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# GameTree.value_optStrategy_eq

Topic: equilibria   Node: dd5a3dd25d17

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value_optStrategy_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At a node, the `optStrategy` picks a child whose value equals the node's value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- At a node, the `optStrategy` picks a child whose value equals the node's value. -/
theorem GameTree.value_optStrategy_eq [DecidableLE U] (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    value (optStrategy m h t).val = value (Node m h t) :=
  ((value_Node_eq_some_child_value m h t).choose_spec.2).symm
