import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreePlayerStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeStrategy

/-!
# GameTree.profileStrategy

Topic: equilibria   Node: 1de214ed5fca

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.profileStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeStrategicForm.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Combine a normal-form profile into the global `GameTree.Strategy` used by the game-tree evaluator. At each node, the mover's contingent plan is used.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
variable [DecidableEq N] in
/-- Combine a normal-form profile into the global `GameTree.Strategy` used by the game-tree evaluator. At each node, the mover's contingent plan is used. -/
def GameTree.profileStrategy (σ : N → PlayerStrategy N U) : Strategy N U :=
  fun m h t => σ m m h t
