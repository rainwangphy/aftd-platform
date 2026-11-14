import AFTD.Prelude

/-!
# tree_entanglement_invariant

Topic: quantum_mechanics   Node: 9bbfc9a023f6

Provenance: formalization of a published result. Source: arXiv:2609.20390

For any finite simple graph G, tree_entanglement_invariant G is the graph invariant F(G) = 140 ∑_v d_v^3 - 1020 ∑_{uv ∈ E(G)} d_u d_v - 40 ∑_v d_v^2.
-/

/-- The Katz-Ising entanglement invariant F(T) = 140 ∑ d_v^3 - 1020 ∑_{uv ∈ E} d_u d_v - 40 ∑ d_v^2. -/
def tree_entanglement_invariant {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ := 140 * (∑ v : V, (G.degree v : ℤ) ^ 3) -
   1020 * (∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => (G.degree u : ℤ) * (G.degree v : ℤ), fun _ _ => mul_comm _ _⟩ e) -
   40 * (∑ v : V, (G.degree v : ℤ) ^ 2)
