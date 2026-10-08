import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashAt
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeHasOnlyRootSubgames
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames

Topic: equilibria   Node: 565dcffac396

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If a tree has no proper subgames, root Nash equilibrium already implies subgame perfection on that tree. This is the pure finite-tree form of MSZ Theorem 7.4.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- If a tree has no proper subgames, root Nash equilibrium already implies subgame perfection on that tree. This is the pure finite-tree form of MSZ Theorem 7.4. -/
theorem GameTree.IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames
    {σ : Strategy N U} {g : GameTree N U}
    (hnash : IsNashAt σ g) (hsubgames : HasOnlyRootSubgames g) :
    IsSubgamePerfectOn σ g := by
  intro s hsg i σ' hiv
  have hs : s = g := hsubgames s hsg
  subst hs
  exact hnash i σ' hiv
