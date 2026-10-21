import AFTD.Prelude

/-!
# simple_graph_clique_four_glued_clique

Topic: graphs   Node: 44892ab8b56c

Provenance: original. Related work: arXiv:2610.27553 (A proof of Vince's conjecture on the average order of connected induced subgraphs): generalizes the extremal graph G_c of Theorem 1.3(i) (n = 7) to every n

The graph on {0,…,n−1} formed by a clique on {0,1,2,3} and a clique on {3,…,n−1}, sharing the vertex 3.
-/

/-- K_4 and K_{n−3} glued at a vertex, on Fin n: {0,1,2,3} is a clique, {3,…,n−1} is a clique, and they share vertex 3. For n = 7 it is the paper's G_c (two K_4 sharing a vertex). -/
def simple_graph_clique_four_glued_clique (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((i.val ≤ 3 ∧ j.val ≤ 3) ∨ (3 ≤ i.val ∧ 3 ≤ j.val))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl ⟨h.2, h.1⟩) (fun h => Or.inr ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
