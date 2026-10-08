import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanMemMen
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanWorseLeft
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanWorseRight
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.joinWoman_injective

Topic: matching_markets   Node: 73e9e9ed039b

Provenance: formalization of a published result. Source: EconCSLib, `GS.joinWoman_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The join woman-assignment is injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- The join woman-assignment is injective. -/
lemma GS.joinWoman_injective : Function.Injective (joinWoman μ ν hμ hν) := by
  intro j1 j2 he
  set i := joinWoman μ ν hμ hν j1 with hidef
  have h1 : joinWoman μ ν hμ hν j1 = i := hidef.symm
  have h2 : joinWoman μ ν hμ hν j2 = i := he.symm.trans hidef.symm
  rcases joinWoman_mem_men μ ν hμ hν h1 with hm1 | hn1 <;>
    rcases joinWoman_mem_men μ ν hμ hν h2 with hm2 | hn2
  · exact hm1.symm.trans hm2          -- both μ-men of i
  · -- j1 = μ-man, j2 = ν-man
    have a := joinWoman_worse_left μ ν hμ hν h1 hm1   -- idxOf (mPartner ν i) ≤ idxOf j1
    have b := joinWoman_worse_right μ ν hμ hν h2 hn2  -- idxOf (mPartner μ i) ≤ idxOf j2
    rw [hn2] at a; rw [hm1] at b
    exact (List.idxOf_inj (pref_list_mem _ (w.valid i).1 (w.valid i).2 j1)).mp
      (le_antisymm b a)
  · -- j1 = ν-man, j2 = μ-man
    have a := joinWoman_worse_right μ ν hμ hν h1 hn1  -- idxOf (mPartner μ i) ≤ idxOf j1
    have b := joinWoman_worse_left μ ν hμ hν h2 hm2   -- idxOf (mPartner ν i) ≤ idxOf j2
    rw [hm2] at a; rw [hn1] at b
    exact (List.idxOf_inj (pref_list_mem _ (w.valid i).1 (w.valid i).2 j1)).mp
      (le_antisymm b a)
  · exact hn1.symm.trans hn2          -- both ν-men of i
