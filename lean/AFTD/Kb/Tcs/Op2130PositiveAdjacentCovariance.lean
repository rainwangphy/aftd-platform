import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_2130_positive_adjacent_covariance

Topic: online_algorithms   Node: 9b932ba29d20

Provenance: helper lemma. Exact finite counterexample to a negative-correlation route for OP-2130, experiment 37039

For a six-request sequence on a five-vertex path, two adjacent discrepancy coordinates have zero means and positive covariance 1/4 under uniform independent tie coins.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem op_2130_positive_adjacent_covariance :
    let edges : List (Fin 5 × Fin 5) := [(0,1), (1,2), (3,4), (2,3), (1,2), (2,3)]
    let terminal := fun r : Fin 6 → Bool =>
      (edges.zip (carpool_greedy_orientations 5 edges (List.ofFn r))).foldl
        (fun d (e,b) => carpool_step 5 d e b) (fun _ => 0)
    (∑ r : Fin 6 → Bool, terminal r 2 * terminal r 3) = (16 : ℤ) ∧
    (∑ r : Fin 6 → Bool, terminal r 2) = (0 : ℤ) ∧
    (∑ r : Fin 6 → Bool, terminal r 3) = (0 : ℤ) := by
  decide
