import AFTD.Prelude
import AFTD.Kb.Tcs.SomeColorOccursAtMostOnceOfCardLtTwice

/-!
# seven_cycle_six_edge_window_misses_color

Topic: graphs   Node: 0d1c33120491

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

In every four-coloring of seven cyclic positions, some six consecutive positions omit a color.
-/

theorem seven_cycle_six_edge_window_misses_color (f : Fin 7 → Fin 4) :
    ∃ excluded : Fin 7, ∃ k : Fin 4, ∀ i : Fin 7, i ≠ excluded → f i ≠ k := by
  let S : Fin 4 → Finset (Fin 7) := fun k => Finset.univ.filter fun i => f i = k
  obtain ⟨k, hk⟩ := some_color_occurs_at_most_once_of_card_lt_twice f (by decide)
  change (S k).card ≤ 1 at hk
  by_cases h : ∃ i, f i = k
  · obtain ⟨excluded, ho⟩ := h
    refine ⟨excluded, k, ?_⟩
    intro i hne hi
    have hio : i = excluded := Finset.card_le_one.mp hk i
      (by simp [S, hi]) excluded (by simp [S, ho])
    exact hne hio
  · refine ⟨0, k, ?_⟩
    intro i _ hi
    exact h ⟨i, hi⟩
