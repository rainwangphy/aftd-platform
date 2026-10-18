import AFTD.Prelude

/-!
# b3_graph

Topic: graphs   Node: fdc5ba1c9c00

Provenance: formalization of a published result. Source: arXiv:2610.21388 (Stronger spectral bound for clique number), Sec. 2, definition of B_t(n_1,...,n_t) for t = 3, with G_3 = P_3 (the base graph whose quotient matrix M appears in Theorem 2.3 for s = 1); blocks indexed 0, 1, 2 with 2 the middle vertex

The graph B_3(n_0, n_1, n_2) on the disjoint union of blocks of sizes n_0, n_1, n_2: two distinct vertices are adjacent iff they lie in the same block or one of them lies in block 2 (the middle vertex of the path P_3).
-/

/-- `B₃(n₀, n₁, n₂)`: the generalized lexicographic product of the path `P₃` (middle vertex `2`) with the cliques `K_{n₀}, K_{n₁}, K_{n₂}`: each vertex `i` of `P₃` is replaced by a clique on `n i` vertices, and two vertices in different cliques are adjacent when one of them lies in the clique of the middle vertex. -/
def b3_graph (n : Fin 3 → ℕ) : SimpleGraph (Σ i : Fin 3, Fin (n i)) := { Adj := fun x y => x ≠ y ∧ (x.1 = y.1 ∨ x.1 = 2 ∨ y.1 = 2), symm := ⟨fun x y h => ⟨h.1.symm, by rcases h.2 with h | h | h <;> simp [h]⟩⟩, loopless := ⟨fun x h => h.1 rfl⟩ }
