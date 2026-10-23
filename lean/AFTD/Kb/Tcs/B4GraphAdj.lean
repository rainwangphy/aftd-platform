import AFTD.Prelude
import AFTD.Kb.Tcs.B4Graph

/-!
# b4_graph_adj

Topic: graphs   Node: bd96d68e8188

Provenance: helper lemma. arXiv:2610.21388, Section 2

Sanity lemma: two distinct vertices in B_4(n) are adjacent if and only if they belong to the same block, or one is in block 0 and the other in block 1, or one in block 1 and the other in block 3, or one in block 2 and the other in block 3.
-/

/-- Sanity lemma: adjacency in B_4(n) unfolds to: distinct, and same block or one of the edges (0,1), (1,3), (2,3) between blocks. -/
@[simp] theorem b4_graph_adj (n : Fin 4 → ℕ) (x y : Σ i : Fin 4, Fin (n i)) :
    (b4_graph n).Adj x y ↔ x ≠ y ∧ (x.1 = y.1 ∨ (x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 0) ∨
      (x.1 = 1 ∧ y.1 = 3) ∨ (x.1 = 3 ∧ y.1 = 1) ∨ (x.1 = 2 ∧ y.1 = 3) ∨ (x.1 = 3 ∧ y.1 = 2)) := Iff.rfl
