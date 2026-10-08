import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.RsinvFinalState
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSInitState

/-!
# rsinv_stability

Topic: matching_markets   Node: 842e2da768ea

Provenance: formalization of a published result. Source: EconCSLib, `rsinv_stability`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If j strictly prefers i over his final partner, i's final partner has rank ≤ j.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- If j strictly prefers i over his final partner, i's final partner has rank ≤ j. -/
lemma rsinv_stability (w m : Preferences n) (j i : Fin n)
    (hlt : (m.prefs j).idxOf i < (finalState w m).nextChoice j) :
    (w.prefs i).idxOf (gs w m i) ≤ (w.prefs i).idxOf j := by
  have hrs := rsinv_finalState w m j i
  have hi_mem : i ∈ (m.prefs j).take ((finalState w m).nextChoice j) := by
    rw [List.mem_take_iff_idxOf_lt]
    · exact hlt
    · exact pref_list_mem _ (m.valid j).1 (m.valid j).2 i
  obtain ⟨h, hh, hrk⟩ := hrs hi_mem
  -- h = gs w m i (since holding i = some h at finalState)
  have hgs : gs w m i = h := by
    simp only [gs, finalState] at hh ⊢; simp [hh]
  rw [hgs]; exact hrk
