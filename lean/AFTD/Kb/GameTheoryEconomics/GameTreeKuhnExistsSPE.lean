import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOptStrategyIsSubgamePerfect
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# GameTree.Kuhn_exists_SPE

Topic: equilibria   Node: dd73e4d897d6

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Kuhn_exists_SPE`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Kuhn's theorem** (existence form): every finite perfect-information game without chance admits a subgame-perfect equilibrium. The backward-induction strategy `optStrategy` is such an SPE.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- **Kuhn's theorem** (existence form): every finite perfect-information game without chance admits a subgame-perfect equilibrium. The backward-induction strategy `optStrategy` is such an SPE. -/
theorem GameTree.Kuhn_exists_SPE [DecidableLE U] : ∃ σ : Strategy N U, IsSubgamePerfect σ :=
  ⟨optStrategy, optStrategy_isSubgamePerfect⟩
