import AFTD.Prelude
import AFTD.Kb.Tcs.ConeNecklaceGraph

/-!
# cone_necklace_next_radial_adj

Topic: graphs   Node: fb367b38306b

Provenance: helper lemma. Sanity lemma for cone_necklace_graph, used in IN-584.

Each private vertex is adjacent to the next cycle vertex.
-/

theorem cone_necklace_next_radial_adj(m : ℕ) (i : Fin m) :
    (cone_necklace_graph m).Adj
      ⟨(i.val + 1) % m, by exact lt_of_lt_of_le (Nat.mod_lt _ (by have := i.isLt; omega)) (by omega)⟩
      ⟨m + i.val, by omega⟩ := by
  simp only [cone_necklace_graph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  refine ⟨Or.inr ⟨i, Or.inr (Or.inr rfl)⟩, ?_⟩
  intro h
  have hv := congrArg Fin.val h
  change (i.val + 1) % m = m + i.val at hv
  have hi := i.isLt
  have hlt := Nat.mod_lt (i.val + 1) (by omega : 0 < m)
  omega
