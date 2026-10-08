import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.RSInv
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.RsinvStep
import AFTD.Kb.GameTheoryEconomics.DaStepNcLeN
import AFTD.Kb.GameTheoryEconomics.JinvStep
import AFTD.Kb.GameTheoryEconomics.HoldingInjectiveStep

/-!
# rsinv_run

Topic: matching_markets   Node: 44c184371abf

Provenance: formalization of a published result. Source: EconCSLib, `rsinv_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

RSInv over daRun.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- RSInv over daRun. -/
lemma rsinv_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hrs : RSInv w m s)
    (hnc0 : ∀ k : Fin n, s.nextChoice k ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2) :
    RSInv w m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero => exact hrs
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · apply ih
        · exact rsinv_step w m s hrs hnc0
        · exact daStep_nc_le_n w m s hnc0 hj hinj
        · exact jinv_step w m s hj
        · exact holding_injective_step w m s hinj
      · exact hrs
