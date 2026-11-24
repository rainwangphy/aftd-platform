import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# op2130_path_positive_vertex_covariance

Topic: online_algorithms   Node: 2e93d6c9de32

Provenance: helper lemma. OP-2130, obstruction to pairwise negative-correlation variance argument

On a four-vertex path, a fixed eight-request greedy schedule produces two adjacent vertex discrepancies with strictly positive covariance 1/8. Thus pairwise nonpositive correlation cannot justify a uniform interval variance bound.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem op2130_path_positive_vertex_covariance :
    let es : List (Fin 4 × Fin 4) := [(0,1),(1,2),(2,3),(1,2),(0,1),(2,3),(1,2),(0,1)]
    let d : (Fin 8 → Bool) → Fin 4 → ℤ := fun r =>
      (carpool_discrepancies 4 es (carpool_greedy_orientations 4 es (List.ofFn r))).getD 8 (fun _ => 0)
    (∑ r : Fin 8 → Bool, d r 0 * d r 1) = 32 ∧
      (∑ r : Fin 8 → Bool, d r 0) = 0 ∧ (∑ r : Fin 8 → Bool, d r 1) = 0 := by
  decide
