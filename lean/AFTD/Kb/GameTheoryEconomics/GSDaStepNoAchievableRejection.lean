import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.HoldInv
import AFTD.Kb.GameTheoryEconomics.GSNoAchievableRejection
import AFTD.Kb.GameTheoryEconomics.GSIsAchievable
import AFTD.Kb.GameTheoryEconomics.Matching
import AFTD.Kb.GameTheoryEconomics.MatchingIsStable
import AFTD.Kb.GameTheoryEconomics.MatchingMarketOfEquivData
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.GSPrefListMem
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.MatchingMarket
import AFTD.Kb.GameTheoryEconomics.GSIsFreeIff
import AFTD.Kb.GameTheoryEconomics.GSDaStepHolding
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcFree
import AFTD.Kb.GameTheoryEconomics.GSDaStepNcHeld
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# GS.daStep_NoAchievableRejection

Topic: matching_markets   Node: 6a11e6f66997

Provenance: formalization of a published result. Source: EconCSLib, `GS.daStep_NoAchievableRejection`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/Optimal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Inductive step (KEY LEMMA).** `NoAchievableRejection` is preserved by one `daStep`. Also threads `HoldInv` (for the old-holder index bound) and holding-injectivity (a man is held by at most one woman). Proof: reduce `(daStep).holding wj` to its `match` and split on whether `j` had already proposed to `wj` before this round (`hinv` then pins `s.holding wj = some j`) or proposes exactly now (`j ∈ pl wj`). In every branch where some `h ≠ j` ends up holding `wj`, the local `build_block` helper produces a blocking pair `(h, wj)` for the achievability witness `μ`: * `wj` prefers `h` to `j = μ.matchM wj` — because `daStep`'s `argmin`/`if` chose `h` over `j` (and `idxOf` is injective on the Nodup list). * `h` prefers `wj` to his μ-partner `wh` — because `(m.prefs h).idxOf wj ≤ s.nextChoice h` (propTarget identity if `h` just proposed; `HoldInv` if `h` was already holding `wj`), while `hinv` applied to `(h, wh)` forces `s.nextChoice h ≤ (m.prefs h).idxOf wh` (using that `h` is not held by `wh` at `s` — freshness, or injectivity since `h` holds `wj ≠ wh`). A blocking pair contradicts `μ`'s stability, so no such displacement occurs: `wj` keeps/takes `j`, and the invariant is preserved.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- **Inductive step (KEY LEMMA).** `NoAchievableRejection` is preserved by one `daStep`. Also threads `HoldInv` (for the old-holder index bound) and holding-injectivity (a man is held by at most one woman). Proof: reduce `(daStep).holding wj` to its `match` and split on whether `j` had already proposed to `wj` before this round (`hinv` then pins `s.holding wj = some j`) or proposes exactly now (`j ∈ pl wj`). In every branch where some `h ≠ j` ends up holding `wj`, the local `build_block` helper produces a blocking pair `(h, wj)` for the achievability witness `μ`: * `wj` prefers `h` to `j = μ.matchM wj` — because `daStep`'s `argmin`/`if` chose `h` over `j` (and `idxOf` is injective on the Nodup list). * `h` prefers `wj` to his μ-partner `wh` — because `(m.prefs h).idxOf wj ≤ s.nextChoice h` (propTarget identity if `h` just proposed; `HoldInv` if `h` was already holding `wj`), while `hinv` applied to `(h, wh)` forces `s.nextChoice h ≤ (m.prefs h).idxOf wh` (using that `h` is not held by `wh` at `s` — freshness, or injectivity since `h` holds `wj ≠ wh`). A blocking pair contradicts `μ`'s stability, so no such displacement occurs: `wj` keeps/takes `j`, and the invariant is preserved. -/
lemma GS.daStep_NoAchievableRejection (s : DAState n)
    (hhold : HoldInv m s)
    (hinj : ∀ j1 j2 i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2)
    (hinv : NoAchievableRejection w m s) :
    NoAchievableRejection w m (daStep w m s) := by
  intro j wj hach hlt
  obtain ⟨μ, hμ_stable, hμ_match⟩ := hach
  have hach2 : IsAchievable w m j wj := ⟨μ, hμ_stable, hμ_match⟩
  -- `μ` pairs woman `wj` with man `j` (consistency: M = women, W = men).
  have hμ_m : μ.matchM wj = some j := (μ.consistent wj j).mpr hμ_match
  -- Abbreviations matching `daStep`'s inner `let`s.
  set pl : Fin n → List (Fin n) := fun p =>
    (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p))).val.toList with pl_def
  set bn : Fin n → Option (Fin n) := fun p =>
    (pl p).argmin (fun k => (w.prefs p).idxOf k) with bn_def
  -- Every member of `pl wj` is a free man who proposed to `wj` this round.
  have pl_props : ∀ q, q ∈ pl wj →
      isFree s q = true ∧ propTarget m q (s.nextChoice q) = some wj := by
    intro q hq
    rw [pl_def] at hq
    simp only [Multiset.mem_toList, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hq
    exact hq
  -- For a proposer `q`, `wj` sits at index `s.nextChoice q` of `m.prefs q`.
  have proposer_idx : ∀ q, q ∈ pl wj → (m.prefs q).idxOf wj = s.nextChoice q := by
    intro q hq
    obtain ⟨_, hpt⟩ := pl_props q hq
    obtain ⟨hlt', hget⟩ : ∃ h, (m.prefs q)[s.nextChoice q]'h = wj :=
      List.getElem?_eq_some_iff.mp hpt
    rw [← hget, (m.valid q).1.idxOf_getElem _ hlt']
  -- If `j` is free and his cursor points at `wj`, then `j ∈ pl wj`.
  have j_in_pl : isFree s j = true → (m.prefs j).idxOf wj = s.nextChoice j → j ∈ pl wj := by
    intro hfj hidx
    rw [pl_def]
    simp only [Multiset.mem_toList, Finset.mem_val, Finset.mem_filter, Finset.mem_univ,
      true_and, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hfj, ?_⟩
    show (m.prefs j)[s.nextChoice j]? = some wj
    rw [← hidx]
    exact List.getElem?_idxOf (pref_list_mem _ (m.valid j).1 (m.valid j).2 wj)
  -- `idxOf`-injectivity helper on a preference list.
  have idxOf_lt_of_ne : ∀ (p a b : Fin n), a ≠ b →
      (w.prefs p).idxOf a ≤ (w.prefs p).idxOf b → (w.prefs p).idxOf a < (w.prefs p).idxOf b := by
    intro p a b hab hle
    refine lt_of_le_of_ne hle (fun e => hab ?_)
    exact (List.idxOf_inj (pref_list_mem _ (w.valid p).1 (w.valid p).2 a)).mp e
  -- THE BLOCKING-PAIR CONTRADICTION (Gusfield–Irving core).
  -- Given a man `h ≠ j` whom `wj` prefers to `j`, who has proposed to `wj` by
  -- round `s` (idxOf `wj` ≤ his cursor), and who is either free or already
  -- holding `wj`, the pair `(h, wj)` blocks the achievability witness `μ`.
  have build_block : ∀ h : Fin n, h ≠ j →
      (w.prefs wj).idxOf h < (w.prefs wj).idxOf j →
      (m.prefs h).idxOf wj ≤ s.nextChoice h →
      (isFree s h = true ∨ s.holding wj = some h) →
      False := by
    intro h hne hpref hbound hsrc
    -- Man side: `h` strictly prefers `wj` to his μ-partner.
    have hman : strict ((MatchingMarket.ofEquivData w m).prefW h).rel (some wj) (μ.matchW h) := by
      cases hwh : μ.matchW h with
      | none => exact ⟨trivial, not_false⟩
      | some wh =>
          have hwh_ne : wh ≠ wj := by
            intro heq
            have hcon : μ.matchM wj = some h := (μ.consistent wj h).mpr (heq ▸ hwh)
            rw [hμ_m] at hcon
            exact hne (Option.some.inj hcon).symm
          have hnotheld : s.holding wh ≠ some h := by
            rcases hsrc with hfree | hheld
            · exact (isFree_iff s h).mp hfree wh
            · intro hcon; exact hwh_ne (hinj wh wj h hcon hheld)
          have hge : s.nextChoice h ≤ (m.prefs h).idxOf wh := by
            by_contra hlt2; push_neg at hlt2
            exact hnotheld (hinv h wh ⟨μ, hμ_stable, hwh⟩ hlt2)
          have hidx_ne : (m.prefs h).idxOf wj ≠ (m.prefs h).idxOf wh := fun heq =>
            hwh_ne ((List.idxOf_inj (pref_list_mem _ (m.valid h).1 (m.valid h).2 wj)).mp heq).symm
          refine ⟨?_, ?_⟩
          · show (m.prefs h).idxOf wj ≤ (m.prefs h).idxOf wh; omega
          · show ¬ (m.prefs h).idxOf wh ≤ (m.prefs h).idxOf wj; omega
    -- Woman side: `wj` strictly prefers `h` to her μ-partner `j`.
    have hwoman : strict ((MatchingMarket.ofEquivData w m).prefM wj).rel (some h) (μ.matchM wj) := by
      rw [hμ_m]
      exact ⟨by show (w.prefs wj).idxOf h ≤ (w.prefs wj).idxOf j; omega,
             by show ¬ (w.prefs wj).idxOf j ≤ (w.prefs wj).idxOf h; omega⟩
    exact hμ_stable wj h ⟨hwoman, hman⟩
  -- Reduce `(daStep).holding wj` to the canonical `match` and fold `bn`.
  rw [daStep_holding]
  change (match s.holding wj, bn wj with
    | none,   none   => none
    | some h, none   => some h
    | none,   some q => some q
    | some h, some q =>
        if (w.prefs wj).idxOf q < (w.prefs wj).idxOf h then some q else some h) = some j
  -- Dichotomy from `hlt`: either `j` had already proposed to `wj` before this
  -- round, or `j` is free and proposes to `wj` exactly now.
  rcases (by
      by_cases hfj : isFree s j = true
      · rw [daStep_nc_free hfj] at hlt
        rcases Nat.lt_or_ge ((m.prefs j).idxOf wj) (s.nextChoice j) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hfj, by omega⟩
      · simp only [Bool.not_eq_true] at hfj
        rw [daStep_nc_held hfj] at hlt
        exact Or.inl hlt :
      (m.prefs j).idxOf wj < s.nextChoice j ∨
        (isFree s j = true ∧ (m.prefs j).idxOf wj = s.nextChoice j)) with hlt' | ⟨hfj, hidx⟩
  · -- `j` already proposed: `hinv` forces `wj` to currently hold `j`.
    have hsj : s.holding wj = some j := hinv j wj hach2 hlt'
    rw [hsj]
    cases hbq : bn wj with
    | none => rfl
    | some q =>
        show (if (w.prefs wj).idxOf q < (w.prefs wj).idxOf j then some q else some j) = some j
        have hq_pl : q ∈ pl wj := List.argmin_mem hbq
        obtain ⟨hfq, _⟩ := pl_props q hq_pl
        split_ifs with hcmp
        · by_cases hqj : q = j
          · rw [hqj]
          · exact (build_block q hqj hcmp (le_of_eq (proposer_idx q hq_pl)) (Or.inl hfq)).elim
        · rfl
  · -- `j` proposes this round, so `j ∈ pl wj` and `bn wj` is non-`none`.
    have hjpl : j ∈ pl wj := j_in_pl hfj hidx
    cases hbq : bn wj with
    | none =>
        exfalso
        have hnil : pl wj = [] := List.argmin_eq_none.mp (by simpa only [bn_def] using hbq)
        rw [hnil] at hjpl
        simp at hjpl
    | some q =>
        have hq_pl : q ∈ pl wj := List.argmin_mem hbq
        obtain ⟨hfq, _⟩ := pl_props q hq_pl
        have hq_le : (w.prefs wj).idxOf q ≤ (w.prefs wj).idxOf j :=
          List.le_of_mem_argmin hjpl hbq
        cases hsw : s.holding wj with
        | none =>
            show some q = some j
            by_cases hqj : q = j
            · rw [hqj]
            · exact (build_block q hqj (idxOf_lt_of_ne wj q j hqj hq_le)
                (le_of_eq (proposer_idx q hq_pl)) (Or.inl hfq)).elim
        | some h0 =>
            show (if (w.prefs wj).idxOf q < (w.prefs wj).idxOf h0 then some q else some h0)
              = some j
            split_ifs with hcmp
            · by_cases hqj : q = j
              · rw [hqj]
              · exact (build_block q hqj (idxOf_lt_of_ne wj q j hqj hq_le)
                  (le_of_eq (proposer_idx q hq_pl)) (Or.inl hfq)).elim
            · by_cases hh0j : h0 = j
              · rw [hh0j]
              · refine (build_block h0 hh0j ?_ ?_ (Or.inr hsw)).elim
                · -- `wj` prefers `h0` to `j`: idxOf h0 ≤ idxOf q ≤ idxOf j, strict.
                  push_neg at hcmp
                  exact idxOf_lt_of_ne wj h0 j hh0j (le_trans hcmp hq_le)
                · -- `h0` holds `wj`, so by HoldInv `wj` is in his proposed-prefix.
                  have hmem := hhold h0 wj hsw
                  have := (List.mem_take_iff_idxOf_lt
                    (pref_list_mem _ (m.valid h0).1 (m.valid h0).2 wj)).mp hmem
                  omega
