import AFTD.Prelude

/-!
# digraph_18_target_spare

Topic: graphs   Node: b0f0444125ea

Provenance: helper lemma. step towards digraph_18_shared_target_forces_two_cycles

The two spare vertices {16, 17} of the normalized eighteen-vertex shared-target configuration.
-/

/-- The two spare vertices 16, 17. -/
def digraph_18_target_spare : Finset (Fin 18) := Finset.univ.filter fun v => 16 ≤ v.val
