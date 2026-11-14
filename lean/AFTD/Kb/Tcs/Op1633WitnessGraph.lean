import AFTD.Prelude
import AFTD.Kb.Tcs.Op1633WitnessNbrTable

/-!
# op1633_witness_graph

Topic: graphs   Node: 5f7e1d876d7a

Provenance: helper lemma. step towards op_1633_exists_cubic_bipartite_connectivity_two_not_fall_three

The witness graph G* on Fin 12: u is adjacent to v exactly when v occurs in row u of the neighbour table. This is two copies of K3,3 minus an edge, cross-joined.
-/

/-- The 12-vertex cubic bipartite witness graph G*, read off the neighbour table. -/
abbrev op1633_witness_graph : SimpleGraph (Fin 12) := SimpleGraph.mk (fun u v : Fin 12 => v.val ∈ op1633_witness_nbr_table.getD u.val [])
    (Std.Symm.mk (fun u v h => by revert u v h; decide))
    (Std.Irrefl.mk (fun u h => by revert u h; decide))
