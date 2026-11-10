import AFTD.Prelude
import AFTD.Kb.Tcs.MinQAryDeletionCollision
import AFTD.Kb.Tcs.MinBinaryDeletionCollision
import AFTD.Kb.Tcs.BinaryDeletionCollisionEqQAryTwo
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings
import AFTD.Kb.Tcs.BinaryDeletionCollision

/-!
# min_q_ary_deletion_collision_two_eq_min_binary

Topic: information   Node: 7b606c4598b0

Provenance: helper lemma. Helper for OP-1359: its q = 2 case is the k = 2 case of OP-1352.

For all k and n, the minimum q-ary k-deletion collision sum over words of length n with q = 2 equals the minimum binary k-deletion collision sum over binary words of length n.
-/

theorem min_q_ary_deletion_collision_two_eq_min_binary (k n : ℕ) :
    min_q_ary_deletion_collision 2 k n = min_binary_deletion_collision k n := by
  unfold min_q_ary_deletion_collision min_binary_deletion_collision
  rw [dif_pos (Or.inl (by norm_num))]
  congr 1
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, binary_deletion_collision_eq_q_ary_two]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨fun i => finTwoEquiv (w i), by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨_, rfl⟩
