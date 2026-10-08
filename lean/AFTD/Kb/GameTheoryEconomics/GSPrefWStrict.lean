import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.GSMatchWWPartner
import AFTD.Kb.GameTheoryEconomics.GSMatchMMPartner
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.prefW_strict

Topic: matching_markets   Node: f84489a8671d

Provenance: formalization of a published result. Source: EconCSLib, `GS.prefW_strict`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.prefW_strict
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
variable {w m} in
variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν) in
lemma GS.prefW_strict {j a b : Fin n} :
    strict ((MatchingMarket.ofEquivData w m).prefW j).rel (some a) (some b) ↔
      (m.prefs j).idxOf a < (m.prefs j).idxOf b := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (m.prefs j).idxOf a ≤ (m.prefs j).idxOf b := h1
    have e2 : ¬ (m.prefs j).idxOf b ≤ (m.prefs j).idxOf a := h2
    omega
  · intro h
    exact ⟨show (m.prefs j).idxOf a ≤ (m.prefs j).idxOf b by omega,
           show ¬ (m.prefs j).idxOf b ≤ (m.prefs j).idxOf a by omega⟩
