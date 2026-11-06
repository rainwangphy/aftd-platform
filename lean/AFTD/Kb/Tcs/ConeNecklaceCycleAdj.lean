import AFTD.Prelude
import AFTD.Kb.Tcs.ConeNecklaceGraph

/-!
# cone_necklace_cycle_adj

Topic: graphs   Node: a5fb8cb310fa

Provenance: helper lemma. Sanity lemma for the graph definition cone_necklace_graph, used in IN-584.

When m is at least three, successive cycle vertices are adjacent.
-/

theorem cone_necklace_cycle_adj(m : ℕ) (hm : 3 ≤ m) (i : Fin m) :
    (cone_necklace_graph m).Adj ⟨i.val, by omega⟩
      ⟨(i.val + 1) % m, by exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)⟩ := by
  simp only [cone_necklace_graph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  refine ⟨Or.inr ⟨i, Or.inl rfl⟩, ?_⟩
  intro h
  have hv := congrArg Fin.val h
  change i.val = (i.val + 1) % m at hv
  have hi := i.isLt
  by_cases hlt : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = m := by omega
    rw [heq, Nat.mod_self] at hv
    omega
