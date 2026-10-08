import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSStableMeet
import AFTD.Kb.GameTheoryEconomics.MatchingIsBlocking
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.GSMeetEquiv
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSPrefMStrict
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchM
import AFTD.Kb.GameTheoryEconomics.GSPrefWStrict
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchW
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetManMemWomen
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetManLeLeft
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetManLeRight
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.stableMeet_isStable

Topic: matching_markets   Node: 432924d78f56

Provenance: formalization of a published result. Source: EconCSLib, `GS.stableMeet_isStable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The meet of two stable matchings is stable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- The meet of two stable matchings is stable. -/
theorem GS.stableMeet_isStable :
    Matching.IsStable (MatchingMarket.ofEquivData w m) (stableMeet μ ν hμ hν) := by
  intro i j hblock
  obtain ⟨hi, hj⟩ := hblock
  rw [stableMeet_matchM] at hi
  rw [stableMeet_matchW] at hj
  set jw := (meetEquiv μ ν hμ hν).symm j with hjwdef
  have hi' : (w.prefs i).idxOf j < (w.prefs i).idxOf (meetMan μ ν hμ hν i) := prefM_strict.mp hi
  have hj' : (m.prefs j).idxOf i < (m.prefs j).idxOf jw := prefW_strict.mp hj
  have hmeet_jw : meetMan μ ν hμ hν jw = j := (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν hmeet_jw with hm | hn
  · -- `jw` is `j`'s `μ`-woman, so `(i, j)` blocks `μ`.
    refine hμ i j ⟨?_, ?_⟩
    · rw [matchM_mPartner μ hμ i]
      exact prefM_strict.mpr (lt_of_lt_of_le hi' (meetMan_le_left μ ν hμ hν i))
    · rw [matchW_wPartner μ hμ j, hm]; exact prefW_strict.mpr hj'
  · -- `jw` is `j`'s `ν`-woman, so `(i, j)` blocks `ν`.
    refine hν i j ⟨?_, ?_⟩
    · rw [matchM_mPartner ν hν i]
      exact prefM_strict.mpr (lt_of_lt_of_le hi' (meetMan_le_right μ ν hμ hν i))
    · rw [matchW_wPartner ν hν j, hn]; exact prefW_strict.mpr hj'
