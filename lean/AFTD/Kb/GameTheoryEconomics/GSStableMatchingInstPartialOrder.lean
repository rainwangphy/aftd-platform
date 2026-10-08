import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSStableMatching
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingPartner
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSStableMatchingMatchWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.StableMatching.instPartialOrder

Topic: matching_markets   Node: c67c3c206158

Provenance: formalization of a published result. Source: EconCSLib, `GS.StableMatching.instPartialOrder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Men-preference order: `μ ≤ ν` iff every man weakly prefers his `ν`-partner to his `μ`-partner (smaller `idxOf` = more preferred).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
/-- Men-preference order: `μ ≤ ν` iff every man weakly prefers his `ν`-partner to his `μ`-partner (smaller `idxOf` = more preferred). -/
instance GS.StableMatching.instPartialOrder : PartialOrder (StableMatching w m) where
  le μ ν := ∀ j : Fin n, (m.prefs j).idxOf (ν.partner j) ≤ (m.prefs j).idxOf (μ.partner j)
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 j := le_trans (h2 j) (h1 j)
  le_antisymm μ ν h1 h2 := by
    have hpart : ∀ j, μ.partner j = ν.partner j := fun j =>
      (List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 _)).mp
        (le_antisymm (h2 j) (h1 j))
    apply Subtype.ext
    apply Matching.ext
    · funext i
      apply Option.ext; intro k
      rw [μ.1.consistent i k, ν.1.consistent i k,
        matchW_partner μ k, matchW_partner ν k, hpart k]
    · funext j
      rw [matchW_partner μ j, matchW_partner ν j, hpart j]
