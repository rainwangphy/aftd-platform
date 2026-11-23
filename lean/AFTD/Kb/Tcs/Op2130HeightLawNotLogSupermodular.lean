import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolDiscrepancies
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# op2130_height_law_not_log_supermodular

Topic: online_algorithms   Node: 08260153d79c

Provenance: helper lemma. OP-2130, finite repeated-path counterexample

For three fixed requests on a four-vertex path, the cumulative-height distribution assigns counts 1 and 1 to two incomparable profiles, but counts 2 and 0 to their coordinatewise minimum and maximum, so the joint law is not lattice log-supermodular.
-/

theorem op2130_height_law_not_log_supermodular :
    let es : List (Fin 4 × Fin 4) := [(0,1), (2,3), (1,2)]
    let count : ℤ → ℤ → ℤ → ℕ := fun a b c =>
      (Finset.univ.filter fun r : Fin 3 → Bool =>
        let d := ((carpool_discrepancies 4 es (carpool_greedy_orientations 4 es (List.ofFn r))).getD 3 (fun _ => 0))
        d 0 = a ∧ d 0 + d 1 = b ∧ d 0 + d 1 + d 2 = c).card
    count (-1) (-1) 1 = 1 ∧ count 1 (-1) (-1) = 1 ∧
      count (-1) (-1) (-1) = 2 ∧ count 1 (-1) 1 = 0 := by
  decide
