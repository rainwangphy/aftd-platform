import AFTD.Prelude
import AFTD.Kb.Tcs.MinQAryDeletionCollisionTwoEqMinBinary
import AFTD.Kb.Tcs.MinBinaryDeletionCollision
import AFTD.Kb.Tcs.MinQAryDeletionCollision

/-!
# op_1359_q_two_of_binary_two_deletion_law

Topic: information   Node: 90fdfcb597a6

Provenance: helper lemma. The q = 2 case of OP-1359 is exactly the k = 2 case of OP-1352 (equivalently OP-999); this conditional records the reduction.

If the binary two-deletion law holds, that is, (min_binary_deletion_collision 2 n - binom(n,2)) / n^(3/2) tends to 2√2, then the q = 2 case of OP-1359 holds: (min_q_ary_deletion_collision 2 2 n - binom(n,2)) / n^(3/2) tends to 2√2.
-/

theorem op_1359_q_two_of_binary_two_deletion_law
    (h : Filter.Tendsto
      (fun n : ℕ => ((min_binary_deletion_collision 2 n : ℝ) - (Nat.choose n 2 : ℝ)) /
        ((n : ℝ) ^ ((3 : ℝ) / 2)))
      Filter.atTop (nhds (2 * Real.sqrt 2))) :
    Filter.Tendsto
      (fun n : ℕ => ((min_q_ary_deletion_collision 2 2 n : ℝ) - (Nat.choose n 2 : ℝ)) /
        ((n : ℝ) ^ ((3 : ℝ) / 2)))
      Filter.atTop (nhds (2 * Real.sqrt 2)) := by
  simpa only [min_q_ary_deletion_collision_two_eq_min_binary] using h
