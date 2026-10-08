import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.GsBijective
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSIsAchievable
import AFTD.Kb.GameTheoryEconomics.FinalAllWomenHold
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.HoldinvFinalState
import AFTD.Kb.GameTheoryEconomics.GSFinalStateNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.FinalHoldingInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.HoldInv

/-!
# GS.galeShapley_isProposingOptimal

Topic: matching_markets   Node: fcbdfe2176ed

Provenance: formalization of a published result. Source: EconCSLib, `GS.galeShapley_isProposingOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Men-optimal stable matching** (Gale–Shapley 1962, [MSZ 22.10]): in the men-proposing DA, every man's GS partner is at least as preferred (by him) as his partner under *any* other stable matching `μ`. Equivalently: for any stable `μ` pairing man `j` with woman `wj`, the GS output's matching of `j` is ranked at most as high (i.e., as good or better) as `wj` in `m.prefs j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- **Men-optimal stable matching** (Gale–Shapley 1962, [MSZ 22.10]): in the men-proposing DA, every man's GS partner is at least as preferred (by him) as his partner under *any* other stable matching `μ`. Equivalently: for any stable `μ` pairing man `j` with woman `wj`, the GS output's matching of `j` is ranked at most as high (i.e., as good or better) as `wj` in `m.prefs j`. -/
theorem GS.galeShapley_isProposingOptimal
    (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) :
    ∀ (j wj : Fin n), μ.matchW j = some wj →
      (m.prefs j).idxOf ((Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j) ≤
        (m.prefs j).idxOf wj := by
  intro j wj hwj
  -- `(j, wj)` is achievable via `μ`.
  have hach : IsAchievable w m j wj := ⟨μ, hμ, hwj⟩
  -- Let `wjs` be j's GS partner.
  set wjs : Fin n := (Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j with wjs_def
  -- Step 1. `wjs` holds `j` in `finalState`.
  have hwjs_apply : gs w m wjs = j :=
    (Equiv.ofBijective (gs w m) (gs_bijective w m)).apply_symm_apply j
  have hwjs_holds : (finalState w m).holding wjs = some j := by
    obtain ⟨h, hh⟩ := final_all_women_hold w m wjs
    have hgs_h : gs w m wjs = h := by simp [gs, hh]
    rw [hgs_h] at hwjs_apply
    exact hwjs_apply ▸ hh
  -- Step 2. By `HoldInv` at `finalState`, `idxOf wjs < nextChoice j`.
  have hwjs_lt : (m.prefs j).idxOf wjs < (finalState w m).nextChoice j :=
    (List.mem_take_iff_idxOf_lt
        (pref_list_mem _ (m.valid j).1 (m.valid j).2 _)).mp
      (holdinv_finalState w m j wjs hwjs_holds)
  -- Step 3. Case-split on whether `wj` lies inside j's proposed-prefix.
  by_cases hwj_lt : (m.prefs j).idxOf wj < (finalState w m).nextChoice j
  · -- `wj` was proposed to. By the invariant, `wj` must currently hold `j`.
    have hwj_holds : (finalState w m).holding wj = some j :=
      finalState_NoAchievableRejection w m j wj hach hwj_lt
    -- Both `wjs` and `wj` hold `j` — by injectivity, they're equal.
    have hwj_eq_wjs : wj = wjs :=
      final_holding_injective w m wj wjs j hwj_holds hwjs_holds
    rw [hwj_eq_wjs]
  · -- `wj` was not proposed to: `nextChoice j ≤ idxOf wj`.
    push_neg at hwj_lt
    omega
