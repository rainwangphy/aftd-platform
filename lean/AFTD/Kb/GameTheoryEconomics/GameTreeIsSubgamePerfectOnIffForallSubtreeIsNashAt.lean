import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashAt
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.isSubgamePerfectOn_iff_forall_subtree_isNashAt

Topic: equilibria   Node: f6bee4329c92

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.isSubgamePerfectOn_iff_forall_subtree_isNashAt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Root-scoped subgame perfection is equivalent to Nash equilibrium at every subtree of the root. This is the pure finite-tree form of MSZ Definition 7.2.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- Root-scoped subgame perfection is equivalent to Nash equilibrium at every subtree of the root. This is the pure finite-tree form of MSZ Definition 7.2. -/
theorem GameTree.isSubgamePerfectOn_iff_forall_subtree_isNashAt
    {σ : Strategy N U} {g : GameTree N U} :
    IsSubgamePerfectOn σ g ↔ ∀ s : GameTree N U, Subtree s g → IsNashAt σ s :=
  Iff.rfl
