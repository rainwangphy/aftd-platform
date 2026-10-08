import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.HoldingRankMonoStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.DaStepHeldOfFreeProp
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcHeld

/-!
# jinv_step

Topic: matching_markets   Node: 2d635a50217a

Provenance: formalization of a published result. Source: EconCSLib, `jinv_step`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`JInv` is preserved by one `daStep`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- `JInv` is preserved by one `daStep`. -/
lemma jinv_step (w m : Preferences n) (s : DAState n) (hj : JInv m s) :
    JInv m (daStep w m s) := by
  intro i p hp
  -- Helper: if s.holding p = some h, then (daStep s).holding p = some h' for some h'.
  have mono : ∀ h : Fin n, s.holding p = some h →
      ∃ h' : Fin n, (daStep w m s).holding p = some h' :=
    fun h hh => (holding_rank_mono_step w m s p hh).imp fun h' ⟨heq, _⟩ => heq
  by_cases hfi : isFree s i = true
  · -- Man i was free: nc increases by 1, hp : p ∈ take (nc+1) (prefs i).
    rw [daStep_nc_free hfi] at hp
    rcases lt_or_ge (s.nextChoice i) n with hnc_lt | h_ge
    · -- nc < n: take (nc+1) = take nc ++ [(prefs i)[nc]].
      rw [List.take_succ_eq_append_getElem (by rwa [(m.valid i).2])] at hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp_old | hp_eq
      · obtain ⟨h, hh⟩ := hj i p hp_old; exact mono h hh
      · -- p = (prefs i)[nc]: man i proposes to p this round.
        have hpt : propTarget m i (s.nextChoice i) = some p := by
          simp [propTarget, List.getElem?_eq_getElem (by rwa [(m.valid i).2]), hp_eq]
        exact daStep_held_of_free_prop w m s i p hfi hpt
    · -- nc ≥ n: take (nc+1) = take nc = prefs i (since length = n).
      have heq_full : (m.prefs i).take (s.nextChoice i) = m.prefs i :=
        List.take_of_length_le (by rw [(m.valid i).2]; exact h_ge)
      have hmem_take : p ∈ (m.prefs i).take (s.nextChoice i) := by
        rw [heq_full]
        rw [List.take_of_length_le (by rw [(m.valid i).2]; omega)] at hp
        exact hp
      obtain ⟨h, hh⟩ := hj i p hmem_take; exact mono h hh
  · -- Man i was not free: nc unchanged.
    simp only [Bool.not_eq_true] at hfi
    rw [daStep_nc_held hfi] at hp
    obtain ⟨h, hh⟩ := hj i p hp; exact mono h hh
