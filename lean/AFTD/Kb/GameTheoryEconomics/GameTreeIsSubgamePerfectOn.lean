import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
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
# GameTree.IsSubgamePerfectOn

Topic: equilibria   Node: 0eb1018a315d

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsSubgamePerfectOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Root-scoped subgame perfection on the subtrees of a fixed root. `IsSubgamePerfect σ` is global over every `GameTree N U`. This predicate restricts the same no-profitable-deviation condition to subgames that occur inside the chosen root `g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- Root-scoped subgame perfection on the subtrees of a fixed root. `IsSubgamePerfect σ` is global over every `GameTree N U`. This predicate restricts the same no-profitable-deviation condition to subgames that occur inside the chosen root `g`. -/
def GameTree.IsSubgamePerfectOn (σ : Strategy N U) (g : GameTree N U) : Prop :=
  ∀ (s : GameTree N U), Subtree s g →
    ∀ (i : N) (σ' : Strategy N U),
      IVariant i σ σ' → outcome σ' s i ≤ outcome σ s i
