import AFTD.Prelude

/-!
# simple_graph_is_k_independent

Topic: graphs   Node: 8193636580ca

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Sec. 1 (k-independent set: Δ(G[I]) < k).

A vertex set I of a graph G is k-independent when the induced subgraph G[I] has maximum degree less than k: every vertex of I has fewer than k neighbours in I.
-/

/-- A vertex set `I` is `k`-independent when `G[I]` has maximum degree less than `k`. -/
def simple_graph_is_k_independent {V : Type*} (G : SimpleGraph V) (k : ℕ) (I : Finset V) : Prop :=
  ∀ v ∈ I, ({u | u ∈ I ∧ G.Adj v u} : Set V).ncard < k
