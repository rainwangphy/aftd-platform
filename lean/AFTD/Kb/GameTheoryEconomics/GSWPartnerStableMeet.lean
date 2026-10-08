import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSStableMeet
import AFTD.Kb.GameTheoryEconomics.GSStableMeetIsStable
import AFTD.Kb.GameTheoryEconomics.GSMeetEquiv
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchM
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchW
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.wPartner_stableMeet

Topic: matching_markets   Node: 81f35c6b51d4

Provenance: formalization of a published result. Source: EconCSLib, `GS.wPartner_stableMeet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.wPartner_stableMeet
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.wPartner_stableMeet (j : Fin n) :
    wPartner (stableMeet μ ν hμ hν) (stableMeet_isStable μ ν hμ hν) j
      = (meetEquiv μ ν hμ hν).symm j := rfl
