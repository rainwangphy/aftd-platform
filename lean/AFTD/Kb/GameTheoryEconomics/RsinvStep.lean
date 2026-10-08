import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.RSInv
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcFree
import AFTD.Kb.GameTheoryEconomics.HoldingRankMonoStep
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.ProposalRankBound
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcHeld

/-!
# rsinv_step

Topic: matching_markets   Node: f3e02b606ced

Provenance: formalization of a published result. Source: EconCSLib, `rsinv_step`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

RSInv is preserved by one daStep.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- RSInv is preserved by one daStep. -/
lemma rsinv_step (w m : Preferences n) (s : DAState n)
    (hrs : RSInv w m s)
    (hnc0 : ∀ k : Fin n, s.nextChoice k ≤ n) :
    RSInv w m (daStep w m s) := by
  intro j i hi
  by_cases hfj : isFree s j = true
  · rw [daStep_nc_free hfj] at hi
    rcases lt_or_ge (s.nextChoice j) n with hnc_lt | h_ge
    · -- nc < n: take (nc+1) = take nc ++ [proposal]
      rw [List.take_succ_eq_append_getElem (by rwa [(m.valid j).2])] at hi
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi_old | hi_eq
      · -- i was in the old take — rank already good; use rank_mono_step
        obtain ⟨h, hh, hrk⟩ := hrs j i hi_old
        obtain ⟨h', hh', hrk'⟩ := holding_rank_mono_step w m s i hh
        exact ⟨h', hh', Nat.le_trans hrk' hrk⟩
      · -- i = (m.prefs j)[nc] = the new proposal; use proposal_rank_bound
        have hpt : propTarget m j (s.nextChoice j) = some i := by
          simp [propTarget, List.getElem?_eq_getElem (by rwa [(m.valid j).2]), hi_eq]
        exact proposal_rank_bound w m s j i hfj hpt
    · -- nc ≥ n: take (nc+1) = take nc = full list
      have hmem_take : i ∈ (m.prefs j).take (s.nextChoice j) := by
        rw [List.take_of_length_le (by rw [(m.valid j).2]; exact h_ge)]
        rw [List.take_of_length_le (by rw [(m.valid j).2]; omega)] at hi; exact hi
      obtain ⟨h, hh, hrk⟩ := hrs j i hmem_take
      obtain ⟨h', hh', hrk'⟩ := holding_rank_mono_step w m s i hh
      exact ⟨h', hh', Nat.le_trans hrk' hrk⟩
  · -- j not free: nc unchanged
    simp only [Bool.not_eq_true] at hfj
    rw [daStep_nc_held hfj] at hi
    obtain ⟨h, hh, hrk⟩ := hrs j i hi
    obtain ⟨h', hh', hrk'⟩ := holding_rank_mono_step w m s i hh
    exact ⟨h', hh', Nat.le_trans hrk' hrk⟩
