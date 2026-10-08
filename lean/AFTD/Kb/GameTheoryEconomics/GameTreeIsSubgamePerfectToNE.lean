import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium

/-!
# GameTree.IsSubgamePerfect.toNE

Topic: equilibria   Node: e3ed68b83712

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsSubgamePerfect.toNE`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

**SPE ⇒ NE**: every subgame-perfect equilibrium is a Nash equilibrium (at any fixed root game).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- **SPE ⇒ NE**: every subgame-perfect equilibrium is a Nash equilibrium (at any fixed root game). -/
theorem GameTree.IsSubgamePerfect.toNE {σ : Strategy N U} (hspe : IsSubgamePerfect σ)
    (g : GameTree N U) : GameTree.IsNashEquilibrium σ g :=
  fun i σ' hiv => hspe g i σ' hiv
