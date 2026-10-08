import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSJoinWoman
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSJoinWomanEqOr
import AFTD.Kb.GameTheoryEconomics.GSWPartnerEqIff
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.joinWoman_mem_men

Topic: matching_markets   Node: 1850843becf4

Provenance: formalization of a published result. Source: EconCSLib, `GS.joinWoman_mem_men`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `i` is man `j`'s join-partner then `j` is one of `i`'s two men.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- If `i` is man `j`'s join-partner then `j` is one of `i`'s two men. -/
lemma GS.joinWoman_mem_men {j i : Fin n} (h : joinWoman μ ν hμ hν j = i) :
    mPartner μ hμ i = j ∨ mPartner ν hν i = j := by
  rcases joinWoman_eq_or μ ν hμ hν j with he | he
  · exact Or.inl ((wPartner_eq_iff μ hμ).mp (he ▸ h))
  · exact Or.inr ((wPartner_eq_iff ν hν).mp (he ▸ h))
