import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep

/-!
# carpool_greedy_orientations

Topic: online_algorithms   Node: 6d755fbd0f25

Provenance: formalization of a published result. Source: arXiv:2611.00388: Online carpooling against an oblivious adversary; OP-1106

Given a list of edges and a list of tie-breaking coins, randomized greedy carpooling orients each edge toward the endpoint with smaller current indegree-minus-outdegree discrepancy (starting from zero), using the corresponding boolean coin to resolve ties.
-/

/-- The sequence of orientation bits chosen by the randomized greedy carpooling algorithm starting from discrepancy 0, orienting each edge toward the endpoint with smaller current discrepancy and breaking ties using the corresponding coin. -/
def carpool_greedy_orientations (n : ℕ) (edges : List (Fin n × Fin n)) (coins : List Bool) :
    List Bool :=
  let rec aux : List (Fin n × Fin n) → List Bool → (Fin n → ℤ) → List Bool
    | [], _, _ => []
    | _, [], _ => []
    | e :: es, c :: cs, d =>
      let b := if d e.1 < d e.2 then true else if d e.2 < d e.1 then false else c
      b :: aux es cs (carpool_step n d e b)
  aux edges coins (fun _ => 0)
