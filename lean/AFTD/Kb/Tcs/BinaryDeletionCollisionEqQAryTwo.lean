import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryDeletionCollision
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings
import AFTD.Kb.Tcs.BinaryDeletionNumEmbeddings
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# binary_deletion_collision_eq_q_ary_two

Topic: information   Node: 4eed03c25b46

Provenance: helper lemma. Helper for OP-1359: identifies its q = 2 case with the binary collision sum of OP-1352 / OP-999.

For every k, n and binary word w of length n, the binary k-deletion collision sum of w equals the q-ary k-deletion collision sum (q = 2) of the word obtained from w by relabelling Bool as Fin 2.
-/

theorem binary_deletion_collision_eq_q_ary_two (k n : ℕ) (w : Fin n → Bool) :
    binary_deletion_collision k n w =
      ∑ u : Fin (n - k) → Fin 2,
        (q_ary_subsequence_num_embeddings 2 (n - k) n u (fun i => finTwoEquiv.symm (w i))) ^ 2 := by
  unfold binary_deletion_collision
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm) _ _ ?_
  intro u
  simp only [binary_deletion_num_embeddings, q_ary_subsequence_num_embeddings, Equiv.arrowCongr_apply,
    Function.comp_apply, Equiv.apply_eq_iff_eq, Equiv.refl_symm, Equiv.refl_apply]
