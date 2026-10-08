import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.opposed_preferences_women

Topic: matching_markets   Node: becd40ebb219

Provenance: formalization of a published result. Source: EconCSLib, `GS.opposed_preferences_women`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dual of `opposed_preferences`: if woman `i` strictly prefers man `mi` to her `candidate`-man `mi'`, then `mi` strictly prefers his `candidate`-woman to `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- Dual of `opposed_preferences`: if woman `i` strictly prefers man `mi` to her `candidate`-man `mi'`, then `mi` strictly prefers his `candidate`-woman to `i`. -/
theorem GS.opposed_preferences_women
    (candidate : Matching (Fin n) (Fin n))
    (hcandidate : Matching.IsStable (MatchingMarket.ofEquivData w m) candidate)
    {i mi mi' j' : Fin n}
    (hcandidate_i : candidate.matchM i = some mi')
    (hpref : (w.prefs i).idxOf mi < (w.prefs i).idxOf mi')
    (hcandidate_m : candidate.matchW mi = some j') :
    (m.prefs mi).idxOf j' < (m.prefs mi).idxOf i := by
  have hmi_ne : mi ≠ mi' := by
    intro he; rw [he] at hpref; exact (lt_irrefl _ hpref)
  have hi_ne : i ≠ j' := by
    intro he; subst he
    have : candidate.matchM i = some mi := (candidate.consistent i mi).mpr hcandidate_m
    rw [hcandidate_i] at this
    exact hmi_ne (Option.some.inj this).symm
  by_contra hle
  push_neg at hle
  have hlt : (m.prefs mi).idxOf i < (m.prefs mi).idxOf j' := by
    refine lt_of_le_of_ne hle (fun e => hi_ne ?_)
    exact (List.idxOf_inj (pref_list_mem _ (m.valid mi).1 (m.valid mi).2 i)).mp e
  exact hcandidate i mi
    ⟨by rw [hcandidate_i]; exact ⟨by show (w.prefs i).idxOf mi ≤ (w.prefs i).idxOf mi'; omega,
                          by show ¬ (w.prefs i).idxOf mi' ≤ (w.prefs i).idxOf mi; omega⟩,
     by rw [hcandidate_m]; exact ⟨by show (m.prefs mi).idxOf i ≤ (m.prefs mi).idxOf j'; omega,
                          by show ¬ (m.prefs mi).idxOf j' ≤ (m.prefs mi).idxOf i; omega⟩⟩
