import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartnerEqIff
import AFTD.Kb.GameTheoryEconomics.GSOpposedPreferencesWomen
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.meetMan_worse_right

Topic: matching_markets   Node: b8b05ec679ea

Provenance: formalization of a published result. Source: EconCSLib, `GS.meetMan_worse_right`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.meetMan_worse_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.meetMan_worse_right {i j : Fin n}
    (hij : meetMan μ ν hμ hν i = j) (hνij : wPartner ν hν j = i) :
    (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf i := by
  have hνm : mPartner ν hν i = j := (wPartner_eq_iff ν hν).mp hνij
  by_cases heq : mPartner μ hμ i = j
  · have : wPartner μ hμ j = i := (wPartner_eq_iff μ hμ).mpr heq
    rw [this]
  · have hbranch : meetMan μ ν hμ hν i = mPartner ν hν i := by rw [hij, hνm]
    have hlt0 : (w.prefs i).idxOf (mPartner ν hν i) < (w.prefs i).idxOf (mPartner μ hμ i) := by
      by_contra hge
      push_neg at hge
      unfold meetMan at hbranch
      rw [if_pos hge] at hbranch
      exact heq (hbranch.trans hνm)
    rw [hνm] at hlt0
    have hlt : (w.prefs i).idxOf j < (w.prefs i).idxOf (mPartner μ hμ i) := hlt0
    have := opposed_preferences_women μ hμ (mi := j) (mi' := mPartner μ hμ i)
      (j' := wPartner μ hμ j) (matchM_mPartner μ hμ i) hlt (matchW_wPartner μ hμ j)
    omega
