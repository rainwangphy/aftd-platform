import AFTD.Prelude
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings

/-!
# min_q_ary_deletion_collision

Topic: information   Node: 63e111d176c6

Provenance: formalization of a published result. Source: knowledgebase OP-1359

For natural numbers q, k, and n, min_q_ary_deletion_collision q k n is the minimum over all q-ary words w of length n of the sum over all words u of length n - k of the square of the number of embeddings of u in w (or 0 if q = 0 and n > 0).
-/

/-- The minimum k-deletion collision sum over all q-ary words of length n. -/
def min_q_ary_deletion_collision (q k n : ℕ) : ℕ := if h : 0 < q ∨ n = 0 then
    haveI : Nonempty (Fin n → Fin q) := by
      rcases h with hq | hn
      · exact ⟨fun _ => ⟨0, hq⟩⟩
      · subst hn
        exact ⟨fun x => x.elim0⟩
    (Finset.univ.image (fun w : Fin n → Fin q =>
      ∑ u : Fin (n - k) → Fin q, (q_ary_subsequence_num_embeddings q (n - k) n u w) ^ 2)).min'
      (Finset.Nonempty.image Finset.univ_nonempty _)
  else 0
