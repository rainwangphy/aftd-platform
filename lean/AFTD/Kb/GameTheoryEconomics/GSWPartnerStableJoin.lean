import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSStableJoin
import AFTD.Kb.GameTheoryEconomics.GSStableJoinIsStable
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSStableJoinMatchW
import AFTD.Kb.GameTheoryEconomics.GSStableJoinMatchM
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.wPartner_stableJoin

Topic: matching_markets   Node: 91ee0a96443c

Provenance: formalization of a published result. Source: EconCSLib, `GS.wPartner_stableJoin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.wPartner_stableJoin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.wPartner_stableJoin (j : Fin n) :
    wPartner (stableJoin μ ν hμ hν) (stableJoin_isStable μ ν hμ hν) j
      = joinWoman μ ν hμ hν j := rfl
