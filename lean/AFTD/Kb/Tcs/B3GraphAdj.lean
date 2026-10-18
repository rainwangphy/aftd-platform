import AFTD.Prelude
import AFTD.Kb.Tcs.B3Graph

/-!
# b3_graph_adj

Topic: graphs   Node: 030fe43c0f83

Provenance: helper lemma. sanity lemma for b3_graph (arXiv:2610.21388 Theorem 3.1)

Sanity lemma: adjacency in B_3(n_0,n_1,n_2) unfolds to: distinct, and same block or one endpoint in block 2.
-/

@[simp] theorem b3_graph_adj (n : Fin 3 → ℕ) (x y : Σ i : Fin 3, Fin (n i)) :
    (b3_graph n).Adj x y ↔ x ≠ y ∧ (x.1 = y.1 ∨ x.1 = 2 ∨ y.1 = 2) := Iff.rfl
