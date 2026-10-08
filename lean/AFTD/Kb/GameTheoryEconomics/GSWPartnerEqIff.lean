import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSWPartner
import AFTD.Kb.GameTheoryEconomics.GSMPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.wPartner_eq_iff

Topic: matching_markets   Node: a6b7d1986b85

Provenance: formalization of a published result. Source: EconCSLib, `GS.wPartner_eq_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The man-of and woman-of partner maps are inverse to each other.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
/-- The man-of and woman-of partner maps are inverse to each other. -/
lemma GS.wPartner_eq_iff (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) {i j : Fin n} :
    wPartner μ hμ j = i ↔ mPartner μ hμ i = j := by
  constructor
  · intro h
    have h1 : μ.matchW j = some i := by rw [matchW_wPartner μ hμ j, h]
    have h2 : μ.matchM i = some j := (μ.consistent i j).mpr h1
    rw [matchM_mPartner μ hμ i] at h2
    exact Option.some.inj h2
  · intro h
    have h1 : μ.matchM i = some j := by rw [matchM_mPartner μ hμ i, h]
    have h2 : μ.matchW j = some i := (μ.consistent i j).mp h1
    rw [matchW_wPartner μ hμ j] at h2
    exact Option.some.inj h2
