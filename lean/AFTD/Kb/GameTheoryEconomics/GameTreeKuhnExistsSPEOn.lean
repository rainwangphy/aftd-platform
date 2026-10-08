import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectToSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeKuhnExistsSPE
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.Kuhn_exists_SPE_on

Topic: equilibria   Node: 0268e76a93d9

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Kuhn_exists_SPE_on`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Kuhn's theorem, root-scoped SPE form**: every finite perfect-information game without chance has a pure strategy that is subgame-perfect on that root.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- **Kuhn's theorem, root-scoped SPE form**: every finite perfect-information game without chance has a pure strategy that is subgame-perfect on that root. -/
theorem GameTree.Kuhn_exists_SPE_on [DecidableLE U] (g : GameTree N U) :
    ∃ σ : Strategy N U, IsSubgamePerfectOn σ g := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE (N := N) (U := U)
  exact ⟨σ, hspe.toSubgamePerfectOn g⟩
