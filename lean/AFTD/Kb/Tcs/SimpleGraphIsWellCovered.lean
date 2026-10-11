import AFTD.Prelude

/-!
# simple_graph_is_well_covered

Topic: graphs   Node: 36ab993a5198

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Sec. 2 (well-covered: all minimal vertex covers have the same size; the paper notes the equivalence with maximal independent sets used here).

A finite graph is well-covered if all its maximal independent sets have the same cardinality (equivalently, all its minimal vertex covers have the same cardinality, since I is a maximal independent set iff V ∖ I is a minimal vertex cover).
-/

def simple_graph_is_well_covered {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ s t : Finset V, Maximal (fun u : Finset V => G.IsIndepSet (u : Set V)) s →
    Maximal (fun u : Finset V => G.IsIndepSet (u : Set V)) t → s.card = t.card
