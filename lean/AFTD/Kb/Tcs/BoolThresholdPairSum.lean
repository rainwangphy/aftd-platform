import AFTD.Prelude
import AFTD.Kb.Tcs.BoolThresholdMarginalSum

/-!
# bool_threshold_pair_sum

Topic: combinatorics   Node: 166303bc1840

Provenance: helper lemma. Standard finite common-threshold coupling, formalized as a helper for OP-205 / RT-1, arXiv:2610.15635. Used to compress whole-class linear relaxations. This does not prove the remaining shape implication and is not claimed novel or research-level.

Two Boolean threshold coordinates have joint membership sum equal to the minimum of the range length and both capacities.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem bool_threshold_pair_sum (N a b : ℕ) :
    (range N).sum (fun r => (decide (r < a) && decide (r < b)).toNat) =
      min N (min a b) := by
  have hb (r : ℕ) : (decide (r < a) && decide (r < b)) = decide (r < min a b) := by
    by_cases ha : r < a <;> by_cases hb : r < b <;> simp [ha, hb, lt_min_iff]
  simp_rw [hb]
  exact bool_threshold_marginal_sum N (min a b)
