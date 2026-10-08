import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNodeEqSomeChildValue
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# GameTree.optStrategy

Topic: equilibria   Node: cc81c9891d62

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.optStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The canonical backward-induction strategy: at each node, pick a child whose backward-induction value equals the node's value (i.e., a child attaining the argmax for the mover). Noncomputable — uses classical choice via `value_Node_eq_some_child_value`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- The canonical backward-induction strategy: at each node, pick a child whose backward-induction value equals the node's value (i.e., a child attaining the argmax for the mover). Noncomputable — uses classical choice via `value_Node_eq_some_child_value`. -/
noncomputable def GameTree.optStrategy [DecidableLE U] : Strategy N U := fun m h t =>
  ⟨(value_Node_eq_some_child_value m h t).choose,
   (value_Node_eq_some_child_value m h t).choose_spec.1⟩
