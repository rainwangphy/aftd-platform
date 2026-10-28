import AFTD.Prelude

/-!
# bool_threshold_marginal_sum

Topic: combinatorics   Node: 18b03f9a78ba

Provenance: helper lemma. Standard finite common-threshold coupling, formalized as a helper for OP-205 / RT-1, arXiv:2610.15635. Used to compress whole-class linear relaxations. This does not prove the remaining shape implication and is not claimed novel or research-level.

A finite threshold membership sum equals the smaller of its range length and its capacity.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem bool_threshold_marginal_sum (N c : ℕ) :
    (range N).sum (fun r => (decide (r < c)).toNat) = min N c := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    by_cases h : N < c
    · simp only [h, decide_true, Bool.toNat_true]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · simp only [h, decide_false, Bool.toNat_false, add_zero]
      rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
