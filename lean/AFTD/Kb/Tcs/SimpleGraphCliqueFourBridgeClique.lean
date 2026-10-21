import AFTD.Prelude

/-!
# simple_graph_clique_four_bridge_clique

Topic: graphs   Node: 34bf23f0f64b

Provenance: original. Related work: arXiv:2610.27553 (A proof of Vince's conjecture on the average order of connected induced subgraphs): generalizes the extremal graph G_b of Theorem 1.3(ii) (n = 8) to every n

The graph on {0,…,n−1} consisting of a clique on {0,1,2,3}, a clique on {4,…,n−1}, and the edge {3,4}.
-/

/-- K_4 on {0,1,2,3} and K_{n−4} on {4,…,n−1} joined by the single edge 3–4 (a cut edge). For n = 8 it is the paper's G_b. -/
def simple_graph_clique_four_bridge_clique (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((i.val ≤ 3 ∧ j.val ≤ 3) ∨ (4 ≤ i.val ∧ 4 ≤ j.val) ∨
    (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
