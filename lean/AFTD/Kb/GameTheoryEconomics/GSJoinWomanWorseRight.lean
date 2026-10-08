import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartnerEqIff
import AFTD.Kb.GameTheoryEconomics.GSOpposedPreferences
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.joinWoman_worse_right

Topic: matching_markets   Node: 84c7ab2499b3

Provenance: formalization of a published result. Source: EconCSLib, `GS.joinWoman_worse_right`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dual of `joinWoman_worse_left` with the roles of `μ`, `ν` swapped.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- Dual of `joinWoman_worse_left` with the roles of `μ`, `ν` swapped. -/
lemma GS.joinWoman_worse_right {j i : Fin n}
    (hji : joinWoman μ ν hμ hν j = i) (hνji : mPartner ν hν i = j) :
    (w.prefs i).idxOf (mPartner μ hμ i) ≤ (w.prefs i).idxOf j := by
  have hνw : wPartner ν hν j = i := (wPartner_eq_iff ν hν).mpr hνji
  by_cases heq : wPartner μ hμ j = i
  · have : mPartner μ hμ i = j := (wPartner_eq_iff μ hμ).mp heq
    rw [this]
  · have hbranch : joinWoman μ ν hμ hν j = wPartner ν hν j := by rw [hji, hνw]
    have hlt0 : (m.prefs j).idxOf (wPartner ν hν j) < (m.prefs j).idxOf (wPartner μ hμ j) := by
      by_contra hge
      push_neg at hge
      unfold joinWoman at hbranch
      rw [if_pos hge] at hbranch
      exact heq (hbranch.trans hνw)
    rw [hνw] at hlt0
    have hlt : (m.prefs j).idxOf i < (m.prefs j).idxOf (wPartner μ hμ j) := hlt0
    have := opposed_preferences w m μ hμ (wj := i) (wj' := wPartner μ hμ j)
      (m' := mPartner μ hμ i) (matchW_wPartner μ hμ j) hlt (matchM_mPartner μ hμ i)
    omega
