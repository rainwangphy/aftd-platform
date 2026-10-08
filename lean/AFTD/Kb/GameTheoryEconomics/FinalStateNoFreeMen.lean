import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.JInv
import AFTD.Kb.GameTheoryEconomics.JinvInit
import AFTD.Kb.GameTheoryEconomics.InitStateInjective
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSMemFreeMenSet
import AFTD.Kb.GameTheoryEconomics.NcSumGrows
import AFTD.Kb.GameTheoryEconomics.NcSumLeNn

/-!
# finalState_no_free_men

Topic: matching_markets   Node: 6fe70857ddb1

Provenance: formalization of a published result. Source: EconCSLib, `finalState_no_free_men`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At termination, every man is held (no free man remains). Proof: if a free man remained, `nc_sum_grows` would give `n*n + 1 ≤ n*n`, contradiction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- At termination, every man is held (no free man remains). Proof: if a free man remained, `nc_sum_grows` would give `n*n + 1 ≤ n*n`, contradiction. -/
lemma finalState_no_free_men :
    ∀ i : Fin n, isFree (finalState w m) i = false := by
  intro i
  -- Establish the pre-conditions for the fuel-sufficiency lemmas.
  have hnc0 : ∀ j : Fin n, (initState n).nextChoice j ≤ n := by simp [initState]
  have hj0 : JInv m (initState n) := jinv_init m
  have hinj0 := initState_injective (n := n)
  -- By contradiction: suppose some man i is still free in finalState.
  by_contra hfree
  simp only [Bool.not_eq_false] at hfree
  -- freeMenSet (finalState w m) is nonempty.
  have hne : (freeMenSet (finalState w m)).Nonempty :=
    ⟨i, mem_freeMenSet.mpr hfree⟩
  -- nc_sum_grows: 0 + (n*n+1) ≤ ∑ nc at finalState.
  have hgrows := nc_sum_grows w m (n * n + 1) (initState n) hnc0 hj0 hinj0 hne
  simp only [initState, Finset.sum_const_zero] at hgrows
  -- nc_sum_le_nn: ∑ nc at finalState ≤ n*n.
  have hle := nc_sum_le_nn w m (n * n + 1) (initState n) hnc0 hj0 hinj0
    (by simp [initState])
  -- Contradiction: n*n+1 ≤ 0 + (n*n+1) ≤ ∑ nc ≤ n*n.
  simp only [initState] at hle
  omega
