import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.Tcs.G

/-!
# GameTree.IsSubgamePerfect

Topic: equilibria   Node: 74f36382c19b

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsSubgamePerfect`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategy is **subgame-perfect** (SPE) if, at every subtree, no player can strictly improve their payoff by a unilateral deviation — i.e., by switching to any `i`-variant strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- A strategy is **subgame-perfect** (SPE) if, at every subtree, no player can strictly improve their payoff by a unilateral deviation — i.e., by switching to any `i`-variant strategy. -/
def GameTree.IsSubgamePerfect (σ : Strategy N U) : Prop :=
  ∀ (g : GameTree N U) (i : N) (σ' : Strategy N U),
    IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i
