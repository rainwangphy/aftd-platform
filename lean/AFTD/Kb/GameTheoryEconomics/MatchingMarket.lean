import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.Pref

/-!
# MatchingMarket

Topic: matching_markets   Node: b8af260af6f1

Provenance: formalization of a published result. Source: EconCSLib, `MatchingMarket`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A two-sided matching market. `M` and `W` are the two sides (e.g., men and women, hospitals and residents). Each agent has a preference over agents on the other side plus the option of being unmatched (`none`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A two-sided matching market. `M` and `W` are the two sides (e.g., men and women, hospitals and residents). Each agent has a preference over agents on the other side plus the option of being unmatched (`none`). -/
structure MatchingMarket (M W : Type*) where
  /-- Each agent on side `M` has a preference over `Option W`. -/
  prefM : M → Pref (Option W)
  /-- Each agent on side `W` has a preference over `Option M`. -/
  prefW : W → Pref (Option M)
