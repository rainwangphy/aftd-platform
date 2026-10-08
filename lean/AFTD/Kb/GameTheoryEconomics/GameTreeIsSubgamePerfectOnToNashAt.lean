import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashAt
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtreeSelf
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.IsSubgamePerfectOn.toNashAt

Topic: equilibria   Node: 84758057e40e

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsSubgamePerfectOn.toNashAt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Root-scoped subgame perfection implies Nash equilibrium at the same root.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- Root-scoped subgame perfection implies Nash equilibrium at the same root. -/
theorem GameTree.IsSubgamePerfectOn.toNashAt {σ : Strategy N U} {g : GameTree N U}
    (hspe : IsSubgamePerfectOn σ g) : IsNashAt σ g :=
  fun i σ' hiv => hspe g (Subtree.self g) i σ' hiv
