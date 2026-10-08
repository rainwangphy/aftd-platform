import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcFree
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcHeld
import AFTD.Kb.GameTheoryEconomics.GSMemFreeMenSet

/-!
# nc_sum_increase

Topic: matching_markets   Node: 2ab7ccca1b3f

Provenance: formalization of a published result. Source: EconCSLib, `nc_sum_increase`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`∑ nextChoice` strictly increases when free men exist.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- `∑ nextChoice` strictly increases when free men exist. -/
lemma nc_sum_increase (w m : Preferences n) (s : DAState n)
    (hne : (freeMenSet s).Nonempty) :
    ∑ i : Fin n, s.nextChoice i < ∑ i : Fin n, (daStep w m s).nextChoice i := by
  obtain ⟨i0, hi0⟩ := hne
  rw [mem_freeMenSet] at hi0
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hfi : isFree s i = true
    · simp [daStep_nc_free hfi]
    · simp [daStep_nc_held (by simpa using hfi)]
  · exact ⟨i0, Finset.mem_univ _, by simp [daStep_nc_free hi0]⟩
