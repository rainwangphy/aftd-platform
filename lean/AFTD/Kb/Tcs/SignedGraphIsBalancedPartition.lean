import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph

/-!
# SignedGraph.IsBalancedPartition

Topic: combinatorics   Node: 5b66d9096e29

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.1 and Sec. 4.1

A pair of disjoint finsets A and B partitioning the vertex set Finset.univ of a signed graph G is a balance partition if every edge whose endpoints both lie in A or both lie in B has sign 1, and every edge with one endpoint in A and one in B has sign -1.
-/

/-- A bipartition of vertices where internal edges are positive and cross edges are negative. -/
def SignedGraph.IsBalancedPartition {V : Type*} [DecidableEq V] [Fintype V] (G : SignedGraph V) (A B : Finset V) : Prop :=
  (A ∪ B = Finset.univ) ∧ Disjoint A B ∧
  (∀ (u v : V) (h : G.graph.Adj u v),
    ((u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) → G.sgn ⟨s(u, v), h⟩ = 1) ∧
    ((u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) → G.sgn ⟨s(u, v), h⟩ = -1))
