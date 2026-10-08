import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartnerEqIff
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSOpposedPreferencesWomen
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.meetMan_worse_left

Topic: matching_markets   Node: b8fadace3601

Provenance: formalization of a published result. Source: EconCSLib, `GS.meetMan_worse_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.meetMan_worse_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.meetMan_worse_left {i j : Fin n}
    (hij : meetMan μ ν hμ hν i = j) (hμij : wPartner μ hμ j = i) :
    (m.prefs j).idxOf (wPartner ν hν j) ≤ (m.prefs j).idxOf i := by
  have hμm : mPartner μ hμ i = j := (wPartner_eq_iff μ hμ).mp hμij
  by_cases heq : mPartner ν hν i = j
  · have : wPartner ν hν j = i := (wPartner_eq_iff ν hν).mpr heq
    rw [this]
  · have hbranch : meetMan μ ν hμ hν i = mPartner μ hμ i := by rw [hij, hμm]
    have hle : (w.prefs i).idxOf (mPartner μ hμ i) ≤ (w.prefs i).idxOf (mPartner ν hν i) := by
      by_contra hgt
      unfold meetMan at hbranch
      rw [if_neg hgt] at hbranch
      exact heq (hbranch.trans hμm)
    rw [hμm] at hle
    have hlt : (w.prefs i).idxOf j < (w.prefs i).idxOf (mPartner ν hν i) := by
      refine lt_of_le_of_ne hle (fun e => heq ?_)
      exact ((List.idxOf_inj (pref_list_mem _ (w.valid i).1 (w.valid i).2 j)).mp e).symm
    have := opposed_preferences_women ν hν (mi := j) (mi' := mPartner ν hν i)
      (j' := wPartner ν hν j) (matchM_mPartner ν hν i) hlt (matchW_wPartner ν hν j)
    omega
