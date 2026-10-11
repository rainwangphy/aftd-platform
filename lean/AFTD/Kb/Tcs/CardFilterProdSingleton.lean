import AFTD.Prelude
import AFTD.Kb.Tcs.CardFilterSingletonProd

/-!
# card_filter_prod_singleton

Topic: approximation   Node: 9c2c7b216bf7

Provenance: helper lemma. step towards greedy_max_cut_half_edges_lower_bound

The number of directed edges in S × {v} is the number of neighbors of v in S.
-/

/-- The number of directed edges in S × {v} is the number of neighbors of v in S. -/
theorem card_filter_prod_singleton {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    ((S ×ˢ {v}).filter (fun ⟨u, w⟩ => G.Adj u w)).card = (S.filter (fun w => G.Adj v w)).card := by
  rw [Finset.product_singleton, Finset.filter_map, Finset.card_map]
  congr 1
  ext u
  simp [G.adj_comm]
