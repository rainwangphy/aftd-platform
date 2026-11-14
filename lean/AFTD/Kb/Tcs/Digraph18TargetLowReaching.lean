import AFTD.Prelude

/-!
# digraph_18_target_low_reaching

Topic: graphs   Node: 71797e5221d0

Provenance: helper lemma. step towards digraph_18_shared_target_forces_two_cycles

The set S of middle vertices (values 9, …, 15) that send an arc to one of the five low vertices 0, …, 4.
-/

/-- S: the middle vertices 9, …, 15 having an out-neighbour of value below 5. -/
noncomputable def digraph_18_target_low_reaching (D : Digraph (Fin 18)) : Finset (Fin 18) := by
  classical
  exact Finset.univ.filter fun r => 9 ≤ r.val ∧ r.val < 16 ∧ ∃ l : Fin 18, l.val < 5 ∧ D.Adj r l
