import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSStableJoin
import AFTD.Kb.GameTheoryEconomics.MatchingIsBlocking
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.GSJoinEquiv
import AFTD.Kb.GameTheoryEconomics.GSPrefMStrict
import AFTD.Kb.GameTheoryEconomics.GSStableJoinMatchM
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSPrefWStrict
import AFTD.Kb.GameTheoryEconomics.GSStableJoinMatchW
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanMemMen
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanLeLeft
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanLeRight
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.stableJoin_isStable

Topic: matching_markets   Node: 9605ebd80b8a

Provenance: formalization of a published result. Source: EconCSLib, `GS.stableJoin_isStable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The join of two stable matchings is stable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- The join of two stable matchings is stable. -/
theorem GS.stableJoin_isStable :
    Matching.IsStable (MatchingMarket.ofEquivData w m) (stableJoin μ ν hμ hν) := by
  intro i j hblock
  obtain ⟨hi, hj⟩ := hblock
  rw [stableJoin_matchM] at hi
  rw [stableJoin_matchW] at hj
  set jm := (joinEquiv μ ν hμ hν).symm i with hjmdef
  have hi' : (w.prefs i).idxOf j < (w.prefs i).idxOf jm := prefM_strict.mp hi
  have hj' : (m.prefs j).idxOf i < (m.prefs j).idxOf (joinWoman μ ν hμ hν j) := prefW_strict.mp hj
  have hjoin_jm : joinWoman μ ν hμ hν jm = i := (joinEquiv μ ν hμ hν).apply_symm_apply i
  rcases joinWoman_mem_men μ ν hμ hν hjoin_jm with hm | hn
  · -- `jm` is `i`'s `μ`-man, so `(i, j)` blocks `μ`.
    refine hμ i j ⟨?_, ?_⟩
    · rw [matchM_mPartner μ hμ i, hm]; exact prefM_strict.mpr hi'
    · rw [matchW_wPartner μ hμ j]
      exact prefW_strict.mpr (lt_of_lt_of_le hj' (joinWoman_le_left μ ν hμ hν j))
  · -- `jm` is `i`'s `ν`-man, so `(i, j)` blocks `ν`.
    refine hν i j ⟨?_, ?_⟩
    · rw [matchM_mPartner ν hν i, hn]; exact prefM_strict.mpr hi'
    · rw [matchW_wPartner ν hν j]
      exact prefW_strict.mpr (lt_of_lt_of_le hj' (joinWoman_le_right μ ν hμ hν j))
