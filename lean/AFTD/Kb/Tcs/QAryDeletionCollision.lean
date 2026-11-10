import AFTD.Prelude
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings

/-!
# q_ary_deletion_collision

Topic: information   Node: a20432ebde28

Provenance: formalization of a published result. Source: knowledgebase OP-1359

For natural numbers q, k, and n, and a q-ary word w of length n represented as a function from Fin n to Fin q, q_ary_deletion_collision q k n w is the sum over all words u of length n - k of the square of the number of embeddings of u as a subsequence of w.
-/

/-- The k-deletion collision sum of a q-ary word w of length n. -/
def q_ary_deletion_collision (q k n : ℕ) (w : Fin n → Fin q) : ℕ := ∑ u : Fin (n - k) → Fin q, (q_ary_subsequence_num_embeddings q (n - k) n u w) ^ 2
