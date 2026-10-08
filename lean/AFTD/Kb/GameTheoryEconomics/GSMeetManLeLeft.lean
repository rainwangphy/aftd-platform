import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchM
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.meetMan_le_left

Topic: matching_markets   Node: 7107f05b98a9

Provenance: formalization of a published result. Source: EconCSLib, `GS.meetMan_le_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.meetMan_le_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.meetMan_le_left (i : Fin n) :
    (w.prefs i).idxOf (meetMan μ ν hμ hν i) ≤ (w.prefs i).idxOf (mPartner μ hμ i) := by
  unfold meetMan; split_ifs with h
  · exact le_refl _
  · push_neg at h; omega
