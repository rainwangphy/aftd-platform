import AFTD.Prelude

/-!
# digraph_18_target_parents

Topic: graphs   Node: e0a54c727e93

Provenance: helper lemma. step towards digraph_18_shared_target_forces_two_cycles

The three designated parents {5, 6, 7} of the normalized eighteen-vertex shared-target configuration.
-/

/-- The three designated parent vertices 5, 6, 7 (each sends an arc to the shared target 8). -/
def digraph_18_target_parents : Finset (Fin 18) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val < 8
