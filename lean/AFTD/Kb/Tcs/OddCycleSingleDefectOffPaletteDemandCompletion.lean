import AFTD.Prelude
import AFTD.Kb.Tcs.OddCycleOffPaletteFactorWord
import AFTD.Kb.Tcs.SingleDefectHighStatesOfFactorWord

/-!
# odd_cycle_single_defect_off_palette_demand_completion

Topic: graphs   Node: f11be1899701

Provenance: helper lemma. OP-874 one-defect cycle-demand reduction; experiments 35105–35107.

On every odd cycle, one low-port defect can be completed in four high colors when a nondefect interface demands a color outside the two allowed at the defect.
-/

theorem odd_cycle_single_defect_off_palette_demand_completion
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n)
    (d : Fin n → Fin 4) (a b : Fin 4) (hab : a ≠ b)
    (hoff : ∃ i : Fin n, i ≠ 0 ∧ d i ≠ a ∧ d i ≠ b) :
    ∃ c p q : Fin n → Fin 4,
      (∀ i, c (i - 1) ≠ c i ∧ p i ≠ q i ∧
        p i ≠ c (i - 1) ∧ p i ≠ c i ∧
        q i ≠ c (i - 1) ∧ q i ≠ c i) ∧
      (∀ i, i ≠ 0 → d i = c (i - 1) ∨ d i = c i) ∧
      (p 0 = a ∨ p 0 = b) ∧
      q 1 = c (-1) ∧ p (-1) ≠ q 0 ∧
      (∀ i, i ≠ 0 → i + 1 ≠ 0 → p i ≠ q (i + 1)) := by
  obtain ⟨c, t, u, hc, hd, ht, htu, htlast, ht0, hulast, hu0, hfirst, hint⟩ :=
    odd_cycle_off_palette_factor_word n hn hodd d a b hab hoff
  obtain ⟨p, q, hpq, hp0, hq0, hq1, hlast, hstep⟩ :=
    single_defect_high_states_of_factor_word n hn c t u hc htu ht0 htlast hu0 hulast hfirst hint
  refine ⟨c, p, q, ?_, hd, ?_, hq1, hlast, hstep⟩
  · intro i
    exact ⟨hc i, hpq i⟩
  · simpa only [hp0] using ht
