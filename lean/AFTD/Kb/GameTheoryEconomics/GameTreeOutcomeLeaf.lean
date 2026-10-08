import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.outcome_Leaf

Topic: equilibria   Node: 167b6f58237e

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.outcome_Leaf`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GameTree.outcome_Leaf
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
omit [TotalPreorder U] in
@[simp]
theorem GameTree.outcome_Leaf (σ : Strategy N U) (p : N → U) :
    outcome σ (Leaf p) = p := by
  rw [outcome]
