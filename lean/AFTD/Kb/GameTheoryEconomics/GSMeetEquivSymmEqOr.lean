import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSMeetEquiv
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMeetMan
import AFTD.Kb.GameTheoryEconomics.GSMeetManMemWomen
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchM
import AFTD.Kb.GameTheoryEconomics.GSStableMeetMatchW
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.meetEquiv_symm_eq_or

Topic: matching_markets   Node: 5f94129aa241

Provenance: formalization of a published result. Source: EconCSLib, `GS.meetEquiv_symm_eq_or`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The meet woman of man `j` is one of his two partners (his worse).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- The meet woman of man `j` is one of his two partners (his worse). -/
lemma GS.meetEquiv_symm_eq_or (j : Fin n) :
    (meetEquiv μ ν hμ hν).symm j = wPartner μ hμ j ∨
    (meetEquiv μ ν hμ hν).symm j = wPartner ν hν j := by
  have h : meetMan μ ν hμ hν ((meetEquiv μ ν hμ hν).symm j) = j :=
    (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν h with hm | hn
  · exact Or.inl hm.symm
  · exact Or.inr hn.symm
