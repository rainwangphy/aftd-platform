import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.HoldInv
import AFTD.Kb.GameTheoryEconomics.GSNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.HoldinvStep
import AFTD.Kb.GameTheoryEconomics.HoldingInjectiveStep
import AFTD.Kb.GameTheoryEconomics.GSDaStepNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.daRun_NoAchievableRejection

Topic: matching_markets   Node: 1f442ec7604d

Provenance: formalization of a published result. Source: EconCSLib, `GS.daRun_NoAchievableRejection`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`NoAchievableRejection` is preserved by `daRun` (threading `HoldInv` and holding-injectivity, both also preserved by `daStep`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- `NoAchievableRejection` is preserved by `daRun` (threading `HoldInv` and holding-injectivity, both also preserved by `daStep`). -/
lemma GS.daRun_NoAchievableRejection (fuel : ℕ) (s : DAState n)
    (hhold : HoldInv m s)
    (hinj : ∀ j1 j2 i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2)
    (hinv : NoAchievableRejection w m s) :
    NoAchievableRejection w m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero => exact hinv
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (holdinv_step w m s hhold) (holding_injective_step w m s hinj)
          (daStep_NoAchievableRejection w m s hhold hinj hinv)
      · exact hinv
