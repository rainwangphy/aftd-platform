import AFTD.Prelude
import AFTD.Kb.Physics.TreeDegreeSqSum

/-!
# tree_katz_ising_F

Topic: quantum_mechanics   Node: d6e138be6f1b

Provenance: formalization of a published result. Source: arXiv:2609.20390

For any finite simple graph G on a vertex type V with decidable equality and adjacency, tree_katz_ising_F G is the integer invariant F(G) = 140 ∑_v d_v^3 - 1020 ∑_{vw ∈ E(G)} d_v d_w - 40 ∑_v d_v^2.
-/

/-- The sixth-order Ising entanglement invariant F(G) = 140 ∑ d_v^3 - 1020 ∑ d_v d_w - 40 ∑ d_v^2. -/
def tree_katz_ising_F {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ := 140 * (∑ v : V, (G.degree v : ℤ) ^ 3) - 1020 * (∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun v w => (G.degree v : ℤ) * (G.degree w : ℤ), fun _ _ => mul_comm _ _⟩ e) - 40 * tree_degree_sq_sum G
