import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetEquiv
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSMeetManMemWomen
import AFTD.Kb.GameTheoryEconomics.GSMeetManWorseRight
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchM
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchW
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.stableMeet_ge_left

Topic: matching_markets   Node: 5392002bb746

Provenance: formalization of a published result. Source: EconCSLib, `GS.stableMeet_ge_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.stableMeet_ge_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.stableMeet_ge_left (j : Fin n) :
    (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf ((meetEquiv μ ν hμ hν).symm j) := by
  have h : meetMan μ ν hμ hν ((meetEquiv μ ν hμ hν).symm j) = j :=
    (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν h with hm | hn
  · exact le_of_eq (congrArg (fun x => (m.prefs j).idxOf x) hm)
  · exact meetMan_worse_right μ ν hμ hν h hn
