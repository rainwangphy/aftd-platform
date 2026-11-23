import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# op2130_conditional_variation_seven_counterexample

Topic: online_algorithms   Node: 40b8040ebf83

Provenance: helper lemma. OP-2130, finite repeated-path counterexample

For a fixed seven-request sequence on a six-vertex path and the all-false coin tape, the terminal value of vertex 3 has conditional martingale quadratic variation exactly 67/32, exceeding 2.
-/

theorem op2130_conditional_variation_seven_counterexample :
    let es : List (Fin 6 × Fin 6) := [(4,5), (2,3), (0,1), (1,2), (1,2), (2,3), (3,4)]
    let S : ℕ → ℤ := fun t => ∑ r : Fin 7 → Bool,
      if ∀ i : Fin 7, i.val < t → r i = false then
        ((carpool_discrepancies 6 es (carpool_greedy_orientations 6 es (List.ofFn r))).getD 7 (fun _ => 0)) 3
      else 0
    (∑ t ∈ Finset.range 7, (4 : ℤ)^t * (2 * S (t+1) - S t)^2) = 34304 := by
  set_option maxHeartbeats 2000000 in
    decide
