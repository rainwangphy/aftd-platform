import AFTD.Prelude

/-!
# path_graph_degree_le_two

Topic: graphs   Node: 98769595a69d

Provenance: helper lemma. Helper for arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5 (equality case of the lower bound: the extremal tree is a path).

Every vertex of the path graph P_k has degree at most 2.
-/

theorem path_graph_degree_le_two (k : ℕ) [DecidableRel (SimpleGraph.pathGraph k).Adj]
    (i : Fin k) : (SimpleGraph.pathGraph k).degree i ≤ 2 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((SimpleGraph.pathGraph k).neighborFinset i).card
      ≤ ({(i : ℕ) - 1, (i : ℕ) + 1} : Finset ℕ).card := by
        apply Finset.card_le_card_of_injOn (fun j : Fin k => (j : ℕ))
        · intro j hj
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj] at hj
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          omega
        · intro j _ j' _ h
          exact Fin.ext h
    _ ≤ 2 := Finset.card_le_two
