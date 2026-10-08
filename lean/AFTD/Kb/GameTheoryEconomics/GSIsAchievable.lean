import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.IsAchievable

Topic: matching_markets   Node: c2782a8bc65a

Provenance: formalization of a published result. Source: EconCSLib, `GS.IsAchievable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`IsAchievable w m j wj` says woman `wj` is **achievable** for man `j`: some stable matching pairs them. Recall the codebase convention `MatchingMarket M W` with `M = women, W = men`; man `j`'s partner under `μ` is `μ.matchW j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- `IsAchievable w m j wj` says woman `wj` is **achievable** for man `j`: some stable matching pairs them. Recall the codebase convention `MatchingMarket M W` with `M = women, W = men`; man `j`'s partner under `μ` is `μ.matchW j`. -/
def GS.IsAchievable (j wj : Fin n) : Prop :=
  ∃ μ : Matching (Fin n) (Fin n),
    Matching.IsStable (MatchingMarket.ofEquivData w m) μ ∧ μ.matchW j = some wj
