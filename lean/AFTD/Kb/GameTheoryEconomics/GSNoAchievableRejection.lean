import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsAchievable
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.NoAchievableRejection

Topic: matching_markets   Node: 66dd09c1c616

Provenance: formalization of a published result. Source: EconCSLib, `GS.NoAchievableRejection`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Run-state invariant for proposer optimality. `NoAchievableRejection w m s` says: at state `s`, for every achievable pair `(j, wj)`, if man `j` has already proposed to `wj` (i.e. `idxOf wj < nextChoice j`), then `wj` is currently holding `j`. Contrapositively, `j` has not been *rejected* by `wj`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- Run-state invariant for proposer optimality. `NoAchievableRejection w m s` says: at state `s`, for every achievable pair `(j, wj)`, if man `j` has already proposed to `wj` (i.e. `idxOf wj < nextChoice j`), then `wj` is currently holding `j`. Contrapositively, `j` has not been *rejected* by `wj`. -/
def GS.NoAchievableRejection (s : DAState n) : Prop :=
  ∀ j wj : Fin n, IsAchievable w m j wj →
    (m.prefs j).idxOf wj < s.nextChoice j → s.holding wj = some j
