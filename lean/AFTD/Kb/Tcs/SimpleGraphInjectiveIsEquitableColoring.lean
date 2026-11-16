import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsEquitableColoring

/-!
# simple_graph_injective_is_equitable_coloring

Topic: graphs   Node: 23bb4a2b5583

Provenance: helper lemma. arXiv:2611.18391

For every finite simple graph G on type V and every injective function c : V → α, c satisfies simple_graph_is_equitable_coloring G c.
-/

/-- Every injective coloring of a finite simple graph is an equitable coloring. -/
theorem simple_graph_injective_is_equitable_coloring {V α : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V → α) (hc : Function.Injective c) :
    simple_graph_is_equitable_coloring G c := fun u v huv _ => by rw [hc huv]
