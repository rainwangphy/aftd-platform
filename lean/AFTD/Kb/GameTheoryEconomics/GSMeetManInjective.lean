import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetManMemWomen
import AFTD.Kb.GameTheoryEconomics.GSMeetManWorseLeft
import AFTD.Kb.GameTheoryEconomics.GSMeetManWorseRight
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.meetMan_injective

Topic: matching_markets   Node: ff8ffd432a2c

Provenance: formalization of a published result. Source: EconCSLib, `GS.meetMan_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.meetMan_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.meetMan_injective : Function.Injective (meetMan μ ν hμ hν) := by
  intro i1 i2 he
  set j := meetMan μ ν hμ hν i1 with hjdef
  have h1 : meetMan μ ν hμ hν i1 = j := hjdef.symm
  have h2 : meetMan μ ν hμ hν i2 = j := he.symm.trans hjdef.symm
  rcases meetMan_mem_women μ ν hμ hν h1 with hm1 | hn1 <;>
    rcases meetMan_mem_women μ ν hμ hν h2 with hm2 | hn2
  · exact hm1.symm.trans hm2
  · have a := meetMan_worse_left μ ν hμ hν h1 hm1
    have b := meetMan_worse_right μ ν hμ hν h2 hn2
    rw [hn2] at a; rw [hm1] at b
    exact (List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 i1)).mp
      (le_antisymm b a)
  · have a := meetMan_worse_right μ ν hμ hν h1 hn1
    have b := meetMan_worse_left μ ν hμ hν h2 hm2
    rw [hm2] at a; rw [hn1] at b
    exact (List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 i1)).mp
      (le_antisymm b a)
  · exact hn1.symm.trans hn2
