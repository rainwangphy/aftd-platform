import AFTD.Prelude

/-!
# simple_graph_is_k_star_forming

Topic: graphs   Node: 3b1877ffa86a

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Definition 2.1.

A vertex set S is k-star-forming when, for every vertex v outside S, the induced graph G[S ∪ {v}] contains a copy of the star K_{1,k} that contains v (v as the centre or as a leaf).
-/

/-- A vertex set `S` is `k`-star-forming when every `v ∉ S` lies in a copy of `K_{1,k}` in `G[S ∪ {v}]`. -/
def simple_graph_is_k_star_forming {V : Type*} (G : SimpleGraph V) (k : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → ∃ c : V, ∃ L : Finset V, (c = v ∨ c ∈ S) ∧ (∀ x ∈ L, x = v ∨ x ∈ S) ∧
    L.card = k ∧ (∀ x ∈ L, G.Adj c x) ∧ (v = c ∨ v ∈ L)
