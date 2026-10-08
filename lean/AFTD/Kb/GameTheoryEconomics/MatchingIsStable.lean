import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsBlocking
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Matching.IsStable

Topic: matching_markets   Node: 2e0c53a2cf17

Provenance: formalization of a published result. Source: EconCSLib, `Matching.IsStable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A matching is stable if it has no blocking pair. [MSZ 22.5]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {M W : Type*} in
/-- A matching is stable if it has no blocking pair. [MSZ 22.5] -/
def Matching.IsStable (market : MatchingMarket M W) (μ : Matching M W) : Prop :=
  ∀ m : M, ∀ w : W, ¬ IsBlocking market μ m w
