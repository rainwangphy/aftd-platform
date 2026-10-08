import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.HoldingRankMonoStep

/-!
# holding_rank_mono_run

Topic: matching_markets   Node: 4704bf1877a9

Provenance: formalization of a published result. Source: EconCSLib, `holding_rank_mono_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rank-mono over any `daRun`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- Rank-mono over any `daRun`. -/
lemma holding_rank_mono_run (fuel : ℕ) (s : DAState n) (j : Fin n) {hval : Fin n}
    (hh : s.holding j = some hval) :
    ∃ h' : Fin n, (daRun w m fuel s).holding j = some h' ∧
      (w.prefs j).idxOf h' ≤ (w.prefs j).idxOf hval := by
  induction fuel generalizing s hval with
  | zero   => exact ⟨hval, hh, le_refl _⟩
  | succ k ih =>
      simp only [daRun]
      split_ifs with hne
      · obtain ⟨h1, hh1, hrk1⟩ := holding_rank_mono_step w m s j hh
        obtain ⟨h2, hh2, hrk2⟩ := ih (daStep w m s) hh1
        exact ⟨h2, hh2, Nat.le_trans hrk2 hrk1⟩
      · exact ⟨hval, hh, le_refl _⟩
