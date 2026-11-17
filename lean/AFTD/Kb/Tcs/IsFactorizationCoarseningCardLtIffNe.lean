import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorizationCoarsening
import AFTD.Kb.Tcs.IsFactorizationCoarseningCardLe

/-!
# isFactorizationCoarsening_card_lt_iff_ne

Topic: combinatorics   Node: 7ca25b7cd992

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

A coarsening y of x has fewer elements than x exactly when y differs from x; this justifies reading `y.card < x.card` as `x < y` in the Möbius recursion.
-/

theorem isFactorizationCoarsening_card_lt_iff_ne {x y : Multiset ℕ}
    (h : IsFactorizationCoarsening x y) : y.card < x.card ↔ y ≠ x := by
  constructor
  · rintro hlt rfl; exact lt_irrefl _ hlt
  · intro hne
    rcases lt_or_eq_of_le (isFactorizationCoarsening_card_le h) with hlt | heq
    · exact hlt
    · exfalso; apply hne
      obtain ⟨G, hG, rfl, rfl⟩ := h
      rw [Multiset.card_map, Multiset.card_join] at heq
      clear hne
      induction G using Multiset.induction_on with
      | empty => simp
      | cons g G ih =>
        have hg : g ≠ 0 := hG g (Multiset.mem_cons_self g G)
        have hG' : ∀ g ∈ G, g ≠ 0 := fun g' hg' => hG g' (Multiset.mem_cons_of_mem hg')
        have hle : Multiset.card G ≤ (G.map Multiset.card).sum := by
          calc Multiset.card G = (G.map (fun _ => 1)).sum := by simp
            _ ≤ (G.map Multiset.card).sum :=
              Multiset.sum_map_le_sum_map _ _ (fun g' hg' => Multiset.card_pos.mpr (hG' g' hg'))
        have hgpos := Multiset.card_pos.mpr hg
        simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons] at heq
        have hg1 : Multiset.card g = 1 := by omega
        have hrest : Multiset.card G = (G.map Multiset.card).sum := by omega
        obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hg1
        rw [Multiset.map_cons, Multiset.join_cons, ih hG' hrest]
        simp
