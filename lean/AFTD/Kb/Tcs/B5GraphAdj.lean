import AFTD.Prelude
import AFTD.Kb.Tcs.B5Graph
import AFTD.Kb.Tcs.G5Adj

/-!
# b5_graph_adj

Topic: graphs   Node: 0ffa37b2f8f6

Provenance: helper lemma. sanity lemma for b5_graph

Sanity lemma: adjacency in B_5 unfolds to: distinct, and the same block or adjacent blocks of G_5.
-/

@[simp] theorem b5_graph_adj (n : Fin 5 → ℕ) (x y : Σ i : Fin 5, Fin (n i)) :
    (b5_graph n).Adj x y ↔ x ≠ y ∧ (x.1 = y.1 ∨ g5_adj x.1 y.1) := Iff.rfl
