import AFTD.Prelude

/-!
# card_filter_singleton_prod

Topic: approximation   Node: d63b085826af

Provenance: helper lemma. step towards greedy_max_cut_half_edges_lower_bound

The number of directed edges in {v} × S is the number of neighbors of v in S.
-/

/-- The number of directed edges in {v} × S is the number of neighbors of v in S. -/
theorem card_filter_singleton_prod {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    (({v} ×ˢ S).filter (fun ⟨u, w⟩ => G.Adj u w)).card = (S.filter (fun w => G.Adj v w)).card := by
  rw [Finset.singleton_product, Finset.filter_map, Finset.card_map]
  rfl
