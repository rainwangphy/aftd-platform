import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreePlayerStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeIVariant
import AFTD.Kb.GameTheoryEconomics.GameTreeProfileStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# GameTree.profileStrategy_deviate_variant

Topic: equilibria   Node: cc26a1a314dc

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.profileStrategy_deviate_variant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeStrategicForm.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Replacing player `i`'s normal-form contingent plan produces an `i`-variant global tree strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
variable [DecidableEq N] in
/-- Replacing player `i`'s normal-form contingent plan produces an `i`-variant global tree strategy. -/
theorem GameTree.profileStrategy_deviate_variant (σ : N → PlayerStrategy N U)
    (i : N) (s' : PlayerStrategy N U) :
    IVariant i (profileStrategy σ) (profileStrategy (Function.update σ i s')) := by
  intro m h t hmi
  simp [profileStrategy, hmi]
