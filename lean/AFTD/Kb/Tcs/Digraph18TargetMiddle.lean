import AFTD.Prelude

/-!
# digraph_18_target_middle

Topic: graphs   Node: 9a34dbb59ac8

Provenance: helper lemma. step towards digraph_18_shared_target_forces_two_cycles

The seven middle vertices {9, 10, …, 15} of the normalized eighteen-vertex shared-target configuration.
-/

/-- The seven middle vertices 9, …, 15 (all of them receive an arc from the shared target 8). -/
def digraph_18_target_middle : Finset (Fin 18) := Finset.univ.filter fun v => 9 ≤ v.val ∧ v.val < 16
