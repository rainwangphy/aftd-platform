import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.JinvStep

/-!
# jinv_run

Topic: matching_markets   Node: 9dbbc89f463d

Provenance: formalization of a published result. Source: EconCSLib, `jinv_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`JInv` over `daRun`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- `JInv` over `daRun`. -/
lemma jinv_run (w m : Preferences n) (fuel : ℕ) (s : DAState n) (hj : JInv m s) :
    JInv m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero   => exact hj
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (jinv_step w m s hj)
      · exact hj
