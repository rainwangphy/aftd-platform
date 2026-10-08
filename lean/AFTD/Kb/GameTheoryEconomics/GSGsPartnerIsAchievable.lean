import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSIsAchievable
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.GsBijective
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.MatchingOfGS
import AFTD.Kb.GameTheoryEconomics.GaleShapleyIsStable
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.gs_partner_isAchievable

Topic: matching_markets   Node: edbece177274

Provenance: formalization of a published result. Source: EconCSLib, `GS.gs_partner_isAchievable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The GS output itself witnesses that `gs.symm j` is achievable for `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- The GS output itself witnesses that `gs.symm j` is achievable for `j`. -/
lemma GS.gs_partner_isAchievable (j : Fin n) :
    IsAchievable w m j ((Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j) :=
  ⟨Matching.ofGS (gs w m) (gs_bijective w m), galeShapley_isStable w m, rfl⟩
