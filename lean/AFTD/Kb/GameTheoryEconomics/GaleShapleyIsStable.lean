import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RsinvStability
import AFTD.Kb.GameTheoryEconomics.FinalAllWomenHold
import AFTD.Kb.GameTheoryEconomics.HoldinvFinalState
import AFTD.Kb.GameTheoryEconomics.GsBijective
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.MatchingOfGS
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.MatchingIsBlocking
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.IsPreference

/-!
# galeShapley_isStable

Topic: matching_markets   Node: ca420458ec5c

Provenance: formalization of a published result. Source: EconCSLib, `galeShapley_isStable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Gale-Shapley stability**: the DA output has no blocking pair. The statement is in the *market* frame (`IsBlocking … (i : M) (j : W)`). But `MatchingMarket.ofEquivData w m` **transposes the two sides** (see its docstring), so the market-`M` index `i` is an algorithm *woman* and the market-`W` index `j` is an algorithm *man*. The proof therefore reads in the algorithm frame — `i` a woman, `j` a man — matching the inline comments. Proof (standard deferred acceptance): suppose `(i, j)` blocks. In algorithm terms man `j` strictly prefers woman `i` to his wife, so `j` proposed to `i` at some round: his wife is in his proposed-prefix (`holdinv_finalState`) and `i` is ranked at least as early (`hprefJ`). Then `rsinv_stability` (`RSInv`) gives that at termination woman `i` holds a man she ranks at least as high as `j`, so she does *not* strictly prefer `j` to her partner — contradicting the blocking assumption.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- **Gale-Shapley stability**: the DA output has no blocking pair. The statement is in the *market* frame (`IsBlocking … (i : M) (j : W)`). But `MatchingMarket.ofEquivData w m` **transposes the two sides** (see its docstring), so the market-`M` index `i` is an algorithm *woman* and the market-`W` index `j` is an algorithm *man*. The proof therefore reads in the algorithm frame — `i` a woman, `j` a man — matching the inline comments. Proof (standard deferred acceptance): suppose `(i, j)` blocks. In algorithm terms man `j` strictly prefers woman `i` to his wife, so `j` proposed to `i` at some round: his wife is in his proposed-prefix (`holdinv_finalState`) and `i` is ranked at least as early (`hprefJ`). Then `rsinv_stability` (`RSInv`) gives that at termination woman `i` holds a man she ranks at least as high as `j`, so she does *not* strictly prefer `j` to her partner — contradicting the blocking assumption. -/
theorem galeShapley_isStable :
    Matching.IsStable (MatchingMarket.ofEquivData w m)
                      (Matching.ofGS (gs w m) (gs_bijective w m)) := by
  intro i j
  simp only [Matching.IsBlocking, Matching.ofGS, MatchingMarket.ofEquivData, strict, not_and]
  intro hprefI hprefJ
  -- After the simp+intros, the context is:
  --   hprefI : woman i strictly prefers man j to her current husband gs w m i
  --     (= idxOf j (w.prefs i) ≤ idxOf (gs w m i) ∧ ¬ converse)
  --   hprefJ : man j weakly prefers woman i to his current wife (gs w m).symm j
  --     (the "≤" half of strict; the "¬ ≤" half is the goal to refute, i.e. the
  --      goal is `¬¬ idxOf (gs w m).symm j ≤ idxOf i`, equivalent to `≤`).
  -- Strategy (Roth–Sotomayor): show woman i is in j's already-proposed prefix, so
  -- by `rsinv_stability` she'd already be holding someone she prefers at least as
  -- much as j — contradicting `hprefI`'s strict preference for j over her husband.
  obtain ⟨_, hI_strict⟩ := hprefI
  rw [not_le] at hI_strict
  -- hI_strict : idxOf j (w.prefs i) < idxOf (gs w m i) (w.prefs i)
  -- Step 1. Identify j's wife — the woman matched with j by `gs`.
  set wife : Fin n := (Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j with wife_def
  have hwife_apply : gs w m wife = j :=
    (Equiv.ofBijective (gs w m) (gs_bijective w m)).apply_symm_apply j
  -- Step 2. `wife` actually holds `j` in `finalState` — follow `gs`'s definition.
  have hwife_holds : (finalState w m).holding wife = some j := by
    obtain ⟨h, hh⟩ := final_all_women_hold w m wife
    have hgs : gs w m wife = h := by simp [gs, hh]
    rw [hgs] at hwife_apply
    exact hwife_apply ▸ hh
  -- Step 3. By `HoldInv` at `finalState`, the wife is in j's already-proposed prefix.
  have hwife_in : wife ∈ (m.prefs j).take ((finalState w m).nextChoice j) :=
    holdinv_finalState w m j wife hwife_holds
  have hj_prefs_mem : ∀ x : Fin n, x ∈ m.prefs j :=
    pref_list_mem _ (m.valid j).1 (m.valid j).2
  have hwife_lt : (m.prefs j).idxOf wife < (finalState w m).nextChoice j :=
    (List.mem_take_iff_idxOf_lt (hj_prefs_mem wife)).mp hwife_in
  -- Step 4. By `hprefJ` (j weakly prefers i to wife), `i` is at least as early as
  -- wife in `m.prefs j`, so also in the proposed prefix.
  have hi_lt : (m.prefs j).idxOf i < (finalState w m).nextChoice j :=
    lt_of_le_of_lt hprefJ hwife_lt
  -- Step 5. `rsinv_stability` then says i's husband is *at least* as preferred
  -- (by i) as j — directly contradicting i's strict preference for j.
  exact absurd (rsinv_stability w m j i hi_lt) (not_le.mpr hI_strict)
