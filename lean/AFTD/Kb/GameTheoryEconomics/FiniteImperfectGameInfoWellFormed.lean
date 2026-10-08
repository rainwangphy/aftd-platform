import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSameMoverOnInfo
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSameActionsOnInfo
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameNoChanceOnDecisionInfo

/-!
# FiniteImperfectGame.InfoWellFormed

Topic: equilibria   Node: 612d84a71cbb

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.InfoWellFormed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Basic well-formedness package for information-set reasoning.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- Basic well-formedness package for information-set reasoning. -/
def FiniteImperfectGame.InfoWellFormed : Prop :=
  G.SameMoverOnInfo ∧ G.SameActionsOnInfo ∧ G.NoChanceOnDecisionInfo
