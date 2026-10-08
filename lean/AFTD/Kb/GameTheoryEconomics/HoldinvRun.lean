import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.HoldInv
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.HoldinvStep

/-!
# holdinv_run

Topic: matching_markets   Node: 35c8d05ac748

Provenance: formalization of a published result. Source: EconCSLib, `holdinv_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

holdinv_run
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
lemma holdinv_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hh : HoldInv m s) : HoldInv m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero => exact hh
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (holdinv_step w m s hh)
      · exact hh
