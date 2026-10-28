import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStrongProd

/-!
# simple_graph_strong_prod_adj_iff

Topic: combinatorics   Node: db53906de249

Provenance: helper lemma. folklore

In the strong product of simple graphs G and H, two pairs x and y are adjacent if and only if x ≠ y, (x.1 = y.1 or G.Adj x.1 y.1), and (x.2 = y.2 or H.Adj x.2 y.2).
-/

/-- Characterization of adjacency in the strong product of two simple graphs. -/
theorem simple_graph_strong_prod_adj_iff {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) (x y : α × β) :
    (simple_graph_strong_prod G H).Adj x y ↔
      x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2) := by
  rfl
