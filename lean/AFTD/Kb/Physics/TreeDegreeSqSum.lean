import AFTD.Prelude

/-!
# tree_degree_sq_sum

Topic: quantum_mechanics   Node: 5520ae278d9b

Provenance: formalization of a published result. Source: arXiv:2609.20390

For any finite type V and simple graph G on V with decidable adjacency, tree_degree_sq_sum G is the integer (with codomain ℤ) defined as the sum over all vertices v : V of the square of the vertex degree G.degree v cast to ℤ: ∑ v : V, (G.degree v : ℤ) ^ 2.
-/

/-- Sum of squared vertex degrees of a simple graph cast to the integers (first Zagreb index D(G)). -/
def tree_degree_sq_sum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ := ∑ v : V, (G.degree v : ℤ) ^ 2
