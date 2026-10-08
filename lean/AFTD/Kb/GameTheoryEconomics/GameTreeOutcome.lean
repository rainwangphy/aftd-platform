import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeSizeMemChildrenLt
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeSize
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.outcome

Topic: equilibria   Node: d13cf5c9ed45

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.outcome`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The outcome (terminal payoff vector) of playing strategy `σ` starting from game tree `g`. Walks down the tree, using `σ` to pick a child at each `Node`, until a `Leaf` is reached.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- The outcome (terminal payoff vector) of playing strategy `σ` starting from game tree `g`. Walks down the tree, using `σ` to pick a child at each `Node`, until a `Leaf` is reached. -/
noncomputable def GameTree.outcome (σ : Strategy N U) : GameTree N U → (N → U)
  | Leaf p => p
  | Node m h t => outcome σ (σ m h t).val
termination_by g => g.size
decreasing_by
  have hmem := (σ m h t).property
  exact size_mem_children_lt m h t (by simpa [children] using hmem)
