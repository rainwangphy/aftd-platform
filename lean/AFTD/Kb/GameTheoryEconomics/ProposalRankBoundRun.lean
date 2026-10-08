import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.ProposalRankBound
import AFTD.Kb.GameTheoryEconomics.HoldingRankMonoRun

/-!
# proposal_rank_bound_run

Topic: matching_markets   Node: b9c658a6c4cf

Provenance: formalization of a published result. Source: EconCSLib, `proposal_rank_bound_run`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Over a daRun, if man j proposed to woman i at the first step, woman i's final partner has rank ≤ j's rank in w.prefs i.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- Over a daRun, if man j proposed to woman i at the first step, woman i's final partner has rank ≤ j's rank in w.prefs i. -/
lemma proposal_rank_bound_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (j i : Fin n) (hfj : isFree s j = true) (hpt : propTarget m j (s.nextChoice j) = some i) :
    ∃ h : Fin n, (daRun w m fuel (daStep w m s)).holding i = some h ∧
      (w.prefs i).idxOf h ≤ (w.prefs i).idxOf j := by
  obtain ⟨h0, hh0, hrk0⟩ := proposal_rank_bound w m s j i hfj hpt
  obtain ⟨h1, hh1, hrk1⟩ := holding_rank_mono_run w m fuel (daStep w m s) i hh0
  exact ⟨h1, hh1, Nat.le_trans hrk1 hrk0⟩
