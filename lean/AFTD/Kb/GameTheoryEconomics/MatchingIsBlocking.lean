import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Matching.IsBlocking

Topic: matching_markets   Node: 505cab948128

Provenance: formalization of a published result. Source: EconCSLib, `Matching.IsBlocking`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pair `(m, w)` is a blocking pair for matching `μ` if both `m` and `w` strictly prefer each other to their current partners. [MSZ 22.5]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {M W : Type*} in
/-- A pair `(m, w)` is a blocking pair for matching `μ` if both `m` and `w` strictly prefer each other to their current partners. [MSZ 22.5] -/
def Matching.IsBlocking (market : MatchingMarket M W) (μ : Matching M W)
    (m : M) (w : W) : Prop :=
  strict (market.prefM m) (some w) (μ.matchM m) ∧
  strict (market.prefW w) (some m) (μ.matchW w)
