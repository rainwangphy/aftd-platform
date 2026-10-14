import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_packing_number_eq_zero_of_clique_free

Topic: graphs   Node: a09051afc3f5

Provenance: helper lemma. Sanity lemma for the triangle packing number, arXiv:2610.15539 (Tuza's conjecture under an edge-count condition).

A triangle-free graph has triangle packing number 0.
-/

theorem simple_graph_triangle_packing_number_eq_zero_of_clique_free {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (h : G.CliqueFree 3) : simple_graph_triangle_packing_number G = 0 := by
  unfold simple_graph_triangle_packing_number
  have : {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) ∧
      (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} = {0} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨T, hT, -, rfl⟩
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      exact fun t ht => h t (hT t ht)
    · rintro rfl
      exact ⟨∅, by simp, by simp, rfl⟩
  rw [this, csSup_singleton]
