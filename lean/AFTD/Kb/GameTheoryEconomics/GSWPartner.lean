import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingPerfect
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.wPartner

Topic: matching_markets   Node: 9fd5617593a1

Provenance: formalization of a published result. Source: EconCSLib, `GS.wPartner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The woman partnered to man `j` under a stable matching `μ` (total, since a stable matching of the balanced market is perfect).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
/-- The woman partnered to man `j` under a stable matching `μ` (total, since a stable matching of the balanced market is perfect). -/
noncomputable def GS.wPartner (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) (j : Fin n) : Fin n :=
  (μ.matchW j).get ((stable_matching_perfect w m μ hμ).2 j)
