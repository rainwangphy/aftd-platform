import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcFree
import AFTD.Kb.GameTheoryEconomics.NotFreeOfNcGe
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcHeld

/-!
# daStep_nc_le_n

Topic: matching_markets   Node: a02f02d32120

Provenance: formalization of a published result. Source: EconCSLib, `daStep_nc_le_n`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`nextChoice i ≤ n` for `daStep`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- `nextChoice i ≤ n` for `daStep`. -/
lemma daStep_nc_le_n (w m : Preferences n) (s : DAState n)
    (hnc0 : ∀ i : Fin n, s.nextChoice i ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (i : Fin n) : (daStep w m s).nextChoice i ≤ n := by
  by_cases hfi : isFree s i = true
  · rw [daStep_nc_free hfi]
    by_contra h_gt; push_neg at h_gt
    exact absurd (not_free_of_nc_ge m s i hj hinj (by omega)) (by simp [hfi])
  · rw [daStep_nc_held (by simpa using hfi)]; exact hnc0 i
