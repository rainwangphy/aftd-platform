import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# GameTree.IVariant

Topic: equilibria   Node: 9b1c0653db40

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IVariant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two strategies are `i`-variants if they agree on all nodes NOT owned by `i`. I.e., `σ'` is obtained from `σ` by changing only player `i`'s choices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- Two strategies are `i`-variants if they agree on all nodes NOT owned by `i`. I.e., `σ'` is obtained from `σ` by changing only player `i`'s choices. -/
def GameTree.IVariant (i : N) (σ σ' : Strategy N U) : Prop :=
  ∀ (m : N) (h : GameTree N U) (t : List (GameTree N U)),
    m ≠ i → σ m h t = σ' m h t
