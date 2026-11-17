import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorizationCoarsening

/-!
# isFactorizationCoarsening_card_le

Topic: combinatorics   Node: 7e10778f9e92

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

A coarsening has at most as many elements as the multiset it coarsens.
-/

theorem isFactorizationCoarsening_card_le {x y : Multiset ℕ}
    (h : IsFactorizationCoarsening x y) : y.card ≤ x.card := by
  obtain ⟨G, hG, rfl, rfl⟩ := h
  rw [Multiset.card_map, Multiset.card_join]
  calc Multiset.card G = (G.map (fun _ => 1)).sum := by simp
    _ ≤ (G.map Multiset.card).sum := by
        apply Multiset.sum_map_le_sum_map
        intro g hg
        exact Multiset.card_pos.mpr (hG g hg)
