import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameInfoWellFormed
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSubgameAt
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameNoChanceOnDecisionInfo
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSameActionsOnInfo
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSameMoverOnInfo

/-!
# FiniteImperfectGame.subgameAt_infoWellFormed

Topic: equilibria   Node: 30b616cf2f19

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.subgameAt_infoWellFormed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Re-rooting a finite imperfect-information game preserves the local information-set well-formedness package.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- Re-rooting a finite imperfect-information game preserves the local information-set well-formedness package. -/
theorem FiniteImperfectGame.subgameAt_infoWellFormed {s : G.State} (h : G.InfoWellFormed) :
    (G.subgameAt s).InfoWellFormed := by
  simpa [subgameAt, InfoWellFormed, SameMoverOnInfo, SameActionsOnInfo,
    NoChanceOnDecisionInfo] using h
