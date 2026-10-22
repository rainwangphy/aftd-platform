import AFTD.Prelude

/-!
# simple_graph_has_star_decomposition

Topic: graphs   Node: 4971f4ef65d6

Provenance: original. Related work: arXiv:2610.07034 Corollary 1.2

A simple graph G has a star decomposition into copies of the star graph K_{1,q} if its edge set can be partitioned into a pairwise disjoint family of subsets of size q such that each subset of edges shares a common vertex.
-/

/-- A simple graph G admits a star decomposition into copies of K_{1,q} if its edge set can be partitioned into sets of size q, each of which forms a star graph. -/
def simple_graph_has_star_decomposition {V : Type*} (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∃ P : Set (Set (Sym2 V)),
    ⋃₀ P = G.edgeSet ∧
    Set.PairwiseDisjoint P id ∧
    (∀ s ∈ P, s.ncard = q) ∧
    ∀ s ∈ P, ∃ v : V, ∀ e ∈ s, v ∈ e
