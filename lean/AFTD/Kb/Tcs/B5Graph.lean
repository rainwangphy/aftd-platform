import AFTD.Prelude
import AFTD.Kb.Tcs.G5Adj
import AFTD.Kb.Tcs.G5AdjSymm

/-!
# b5_graph

Topic: graphs   Node: bc8fbaa6ff47

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Sec. 2, definition of B_t for t = 5

The graph B_5(n_1..n_5) of arXiv:2610.21388: each vertex i of G_5 is replaced by a clique of n_i vertices, and cliques of adjacent vertices of G_5 are completely joined.
-/

/-- `B₅(n₀, …, n₄)`: the generalized lexicographic product of `G₅` with cliques `K_{n₀}, …, K_{n₄}`: two distinct vertices are adjacent iff they lie in the same block or their blocks are adjacent in `G₅`. -/
def b5_graph (n : Fin 5 → ℕ) : SimpleGraph (Σ i : Fin 5, Fin (n i)) := { Adj := fun x y => x ≠ y ∧ (x.1 = y.1 ∨ g5_adj x.1 y.1), symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp Eq.symm (g5_adj_symm _ _)⟩⟩, loopless := ⟨fun _ h => h.1 rfl⟩ }
