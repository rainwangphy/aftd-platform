import AFTD.Prelude

/-!
# simple_graph_is_chain_graph

Topic: graphs   Node: 4623311f6eea

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Sec. 6 (chain graphs: bipartite graphs whose neighbourhoods on one side are nested).

G is a chain graph with bipartition (A, V \ A): every edge joins A to its complement, and the neighbourhoods of the vertices of A are totally ordered by inclusion.
-/

/-- A chain graph with bipartition `(A, Aᶜ)`: bipartite, with the neighbourhoods of the vertices of `A` nested. -/
def simple_graph_is_chain_graph {V : Type*} (G : SimpleGraph V) (A : Set V) : Prop :=
  (∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A)) ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, G.neighborSet a₁ ⊆ G.neighborSet a₂ ∨ G.neighborSet a₂ ⊆ G.neighborSet a₁
