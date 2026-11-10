import AFTD.Prelude
import AFTD.Kb.Tcs.MinQAryDeletionCollision

/-!
# min_q_ary_deletion_collision_three_three_five

Topic: information   Node: 85214ffa13ac

Provenance: helper lemma. Small case of OP-1359 (q = 3, n = 5); value from experiment 21007, attained by 01210.

The minimum, over ternary words of length 5, of the 3-deletion collision sum is 14, so C_3(5) - binom(5,3) = 4.
-/

theorem min_q_ary_deletion_collision_three_three_five : min_q_ary_deletion_collision 3 3 5 = 14 := by decide +kernel
