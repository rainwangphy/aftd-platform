import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.NcSumIncrease
import AFTD.Kb.GameTheoryEconomics.DaStepNcLeN
import AFTD.Kb.GameTheoryEconomics.JinvStep
import AFTD.Kb.GameTheoryEconomics.HoldingInjectiveStep
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# nc_sum_grows

Topic: matching_markets   Node: 9004eedcd05c

Provenance: formalization of a published result. Source: EconCSLib, `nc_sum_grows`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

After `fuel` rounds ending with free men, `∑ nextChoice` grew by ≥ `fuel`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- After `fuel` rounds ending with free men, `∑ nextChoice` grew by ≥ `fuel`. -/
lemma nc_sum_grows (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hnc0 : ∀ i : Fin n, s.nextChoice i ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (hne_end : (freeMenSet (daRun w m fuel s)).Nonempty) :
    ∑ i : Fin n, s.nextChoice i + fuel ≤ ∑ i : Fin n, (daRun w m fuel s).nextChoice i := by
  induction fuel generalizing s with
  | zero => simp [daRun]
  | succ k ih =>
      simp only [daRun]
      split_ifs with hne_s
      · -- this round was active
        have hsum_inc := nc_sum_increase w m s hne_s
        -- freeMenSet after k more rounds of daStep s is nonempty
        have hne_k : (freeMenSet (daRun w m k (daStep w m s))).Nonempty := by
          simp only [daRun] at hne_end; simpa [hne_s] using hne_end
        have hih := ih _ (daStep_nc_le_n w m s hnc0 hj hinj) (jinv_step w m s hj)
            (holding_injective_step w m s hinj) hne_k
        linarith
      · -- freeMenSet s = ∅: daRun (k+1) s = s
        simp only [Finset.not_nonempty_iff_eq_empty] at hne_s
        simp only [daRun, hne_s, Finset.not_nonempty_iff_eq_empty, ↓reduceIte] at hne_end
        exact absurd hne_s (Finset.nonempty_iff_ne_empty.mp hne_end)
