import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.GameTreePlayerStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcome
import AFTD.Kb.GameTheoryEconomics.GameTreeProfileStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# GameTree.toStrategicGame

Topic: equilibria   Node: 5daff45dc406

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.toStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeStrategicForm.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The strategic-form extraction of a finite perfect-information tree.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
variable [DecidableEq N] in
/-- The strategic-form extraction of a finite perfect-information tree. -/
noncomputable def GameTree.toStrategicGame (g : GameTree N U) : EconCSLib.StrategicGame N U where
  strategy := fun _ => PlayerStrategy N U
  payoff σ i := outcome (profileStrategy σ) g i
