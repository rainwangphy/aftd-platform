import AFTD.Prelude

/-!
# simple_graph_reconfiguration_graph

Topic: graphs   Node: 677fac568186

Provenance: formalization of a published result. Source: arXiv:2610.27527 Section 1

For a simple graph G and a natural number k, the k-reconfiguration graph of G is the simple graph whose vertices are the proper k-colorings of G with colors in Fin k, where two colorings are adjacent if and only if they differ on exactly one vertex.
-/

/-- The k-reconfiguration graph of proper k-colorings of a simple graph G, with edges between colorings differing at exactly one vertex. -/
def simple_graph_reconfiguration_graph {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (G.Coloring (Fin k)) := {
  Adj := fun c₁ c₂ => ∃! v : V, c₁ v ≠ c₂ v
  symm := ⟨fun _ _ ⟨v, hv, huniq⟩ => ⟨v, ne_comm.mp hv, fun u hu => huniq u (ne_comm.mp hu)⟩⟩
  loopless := ⟨fun _ ⟨_, hv, _⟩ => hv rfl⟩
}
