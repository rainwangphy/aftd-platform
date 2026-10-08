import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.opposed_preferences

Topic: matching_markets   Node: 8a74c3ba8df9

Provenance: formalization of a published result. Source: EconCSLib, `GS.opposed_preferences`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Lattice.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Opposed preferences.** Let `μ` be a stable matching. If man `j` is matched to woman `wj` under another matching `ν` and **strictly prefers** `wj` to his `μ`-partner `wj'`, then `wj` strictly prefers her `μ`-partner `m'` to `j`. Intuition: the two sides' interests are opposed across stable matchings — when a man trades up, the woman he gains trades down. Proof: otherwise `(wj, j)` would be a blocking pair for `μ` (he prefers her to his `μ`-partner by hypothesis; she would prefer him to her `μ`-partner `m'`), contradicting stability. Only `μ` need be stable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} (w m : Preferences n) in
/-- **Opposed preferences.** Let `μ` be a stable matching. If man `j` is matched to woman `wj` under another matching `ν` and **strictly prefers** `wj` to his `μ`-partner `wj'`, then `wj` strictly prefers her `μ`-partner `m'` to `j`. Intuition: the two sides' interests are opposed across stable matchings — when a man trades up, the woman he gains trades down. Proof: otherwise `(wj, j)` would be a blocking pair for `μ` (he prefers her to his `μ`-partner by hypothesis; she would prefer him to her `μ`-partner `m'`), contradicting stability. Only `μ` need be stable. -/
theorem GS.opposed_preferences
    (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
    {j wj wj' m' : Fin n}
    (hμ_j : μ.matchW j = some wj')
    (hpref : (m.prefs j).idxOf wj < (m.prefs j).idxOf wj')
    (hμ_w : μ.matchM wj = some m') :
    (w.prefs wj).idxOf m' < (w.prefs wj).idxOf j := by
  -- `wj ≠ wj'` since `j` strictly prefers `wj` over `wj'`.
  have hwj_ne : wj ≠ wj' := by
    intro he; rw [he] at hpref; exact (lt_irrefl _ hpref)
  -- `j ≠ m'`: else `μ` would match `wj` to `j`, contradicting `μ.matchW j = some wj'`.
  have hj_ne : j ≠ m' := by
    intro he; subst he
    have : μ.matchW j = some wj := (μ.consistent wj j).mp hμ_w
    rw [hμ_j] at this
    exact hwj_ne (Option.some.inj this).symm
  -- Suppose `wj` does NOT strictly prefer `m'` to `j`; derive a blocking pair.
  by_contra hle
  push_neg at hle  -- (w.prefs wj).idxOf j ≤ (w.prefs wj).idxOf m'
  -- `wj` then strictly prefers `j` to `m'` (strictness from `j ≠ m'`).
  have hlt : (w.prefs wj).idxOf j < (w.prefs wj).idxOf m' := by
    refine lt_of_le_of_ne hle (fun e => hj_ne ?_)
    exact (List.idxOf_inj (pref_list_mem _ (w.valid wj).1 (w.valid wj).2 j)).mp e
  -- `(wj, j)` blocks `μ`.
  exact hμ wj j
    ⟨by rw [hμ_w]; exact ⟨by show (w.prefs wj).idxOf j ≤ (w.prefs wj).idxOf m'; omega,
                          by show ¬ (w.prefs wj).idxOf m' ≤ (w.prefs wj).idxOf j; omega⟩,
     by rw [hμ_j]; exact ⟨by show (m.prefs j).idxOf wj ≤ (m.prefs j).idxOf wj'; omega,
                          by show ¬ (m.prefs j).idxOf wj' ≤ (m.prefs j).idxOf wj; omega⟩⟩
