import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartnerEqIff
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSOpposedPreferences
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.joinWoman_worse_left

Topic: matching_markets   Node: bd816927fc83

Provenance: formalization of a published result. Source: EconCSLib, `GS.joinWoman_worse_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `i` is the join-partner of her `μ`-man `j`, then `i` weakly prefers her `ν`-man to `j` (so `j` is her worse man).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- If `i` is the join-partner of her `μ`-man `j`, then `i` weakly prefers her `ν`-man to `j` (so `j` is her worse man). -/
lemma GS.joinWoman_worse_left {j i : Fin n}
    (hji : joinWoman μ ν hμ hν j = i) (hμji : mPartner μ hμ i = j) :
    (w.prefs i).idxOf (mPartner ν hν i) ≤ (w.prefs i).idxOf j := by
  have hμw : wPartner μ hμ j = i := (wPartner_eq_iff μ hμ).mpr hμji
  by_cases heq : wPartner ν hν j = i
  · -- `i` is also `j`'s ν-woman, so `mPartner ν i = j`.
    have : mPartner ν hν i = j := (wPartner_eq_iff ν hν).mp heq
    rw [this]
  · -- `j` strictly prefers `i` (his μ-woman) over his ν-woman; opposed prefs.
    have hbranch : joinWoman μ ν hμ hν j = wPartner μ hμ j := by rw [hji, hμw]
    have hle : (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf (wPartner ν hν j) := by
      by_contra hgt
      unfold joinWoman at hbranch
      rw [if_neg hgt] at hbranch
      exact heq (hbranch.trans hμw)
    rw [hμw] at hle
    have hlt : (m.prefs j).idxOf i < (m.prefs j).idxOf (wPartner ν hν j) := by
      refine lt_of_le_of_ne hle (fun e => heq ?_)
      exact ((List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 i)).mp e).symm
    have := opposed_preferences w m ν hν (wj := i) (wj' := wPartner ν hν j)
      (m' := mPartner ν hν i) (matchW_wPartner ν hν j) hlt (matchM_mPartner ν hν i)
    omega
