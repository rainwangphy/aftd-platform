import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSStableMatching
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstPartialOrder
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingGsStable
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingPartner
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.GsBijective
import AFTD.Kb.GameTheoryEconomics.GSGaleShapleyIsProposingOptimal
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingMatchWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingInstLattice
import AFTD.Kb.GameTheoryEconomics.MatchingMarket

/-!
# GS.StableMatching.gsStable_greatest

Topic: matching_markets   Node: 3adbb0450d51

Provenance: formalization of a published result. Source: EconCSLib, `GS.StableMatching.gsStable_greatest`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**The GS output is the greatest stable matching** in the men-preference order: every man weakly prefers his GS partner to his partner in any other stable matching. This is `galeShapley_isProposingOptimal` packaged as the lattice maximum (`⊤`-like greatest element).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS GS.StableMatching in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- **The GS output is the greatest stable matching** in the men-preference order: every man weakly prefers his GS partner to his partner in any other stable matching. This is `galeShapley_isProposingOptimal` packaged as the lattice maximum (`⊤`-like greatest element). -/
theorem GS.StableMatching.gsStable_greatest [NeZero n] (μ : StableMatching w m) : μ ≤ gsStable w m := by
  intro j
  show (m.prefs j).idxOf ((gsStable w m).partner j) ≤ (m.prefs j).idxOf (μ.partner j)
  have hg : (gsStable w m).partner j
      = (Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j := rfl
  rw [hg]
  exact galeShapley_isProposingOptimal w m μ.1 μ.2 j (μ.partner j) (matchW_partner μ j)
