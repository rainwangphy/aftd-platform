import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# forest_carpool_final_discrepancy

Topic: online_algorithms   Node: 2246bc0cdfc5

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

The final discrepancy of a vertex after greedy orientation of the given edges with the given indexed tie-breaking coins.
-/

def forest_carpool_final_discrepancy (n : ℕ) (edges : List (Fin n × Fin n)) (r : Fin edges.length → Bool) (v : Fin n) : ℤ := ((carpool_discrepancies n edges (carpool_greedy_orientations n edges (List.ofFn r))).getLastD (fun _ => 0)) v
