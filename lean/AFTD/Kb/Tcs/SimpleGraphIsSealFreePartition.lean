import AFTD.Prelude

/-!
# simple_graph_is_seal_free_partition

Topic: graphs   Node: f55cf07243c0

Provenance: helper lemma. step towards quadripartite_minimum_coloring_max_wild_number_eq

A vertex map p : V → Fin q is a seal-free block partition for an edge colouring γ of a graph G when (i) every block {v | p v = i} induces a connected subgraph of G (this also forces every block to be nonempty), and (ii) for every colour γ e of an edge and every nonempty proper set T of block labels, some edge of colour γ e crosses from T to its complement.
-/

/-- A partition of the vertices into connected blocks such that every edge colour crosses every proper nonempty cut of blocks. -/
def simple_graph_is_seal_free_partition {V α : Type*} (G : SimpleGraph V) (γ : G.edgeSet → α)
    (q : ℕ) (p : V → Fin q) : Prop :=
  (∀ i : Fin q, (SimpleGraph.induce {v : V | p v = i} G).Connected) ∧
  ∀ (e : G.edgeSet) (T : Finset (Fin q)), T.Nonempty → T ≠ Finset.univ →
    ∃ (u v : V) (h : G.Adj u v), p u ∈ T ∧ p v ∉ T ∧ γ ⟨s(u, v), by simpa using h⟩ = γ e
