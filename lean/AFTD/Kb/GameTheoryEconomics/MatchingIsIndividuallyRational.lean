import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Matching.IsIndividuallyRational

Topic: matching_markets   Node: 6e0ec8008e0a

Provenance: formalization of a published result. Source: EconCSLib, `Matching.IsIndividuallyRational`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A matching is individually rational if every matched agent strictly prefers their partner to being unmatched.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {M W : Type*} in
/-- A matching is individually rational if every matched agent strictly prefers their partner to being unmatched. -/
def Matching.IsIndividuallyRational (market : MatchingMarket M W) (μ : Matching M W) : Prop :=
  (∀ m : M, ∀ w : W, μ.matchM m = some w → strict (market.prefM m) (some w) none) ∧
  (∀ w : W, ∀ m : M, μ.matchW w = some m → strict (market.prefW w) (some m) none)
