import AFTD.Prelude
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings

/-!
# qary_multiple_deletion_hinge

Topic: information   Node: a715fe3a50be

Provenance: formalization of a published result. Source: knowledgebase, OP-1503

For natural numbers t, q, n, and r, and a q-ary word y of length n (y : Fin n → Fin q), the t-deletion hinge sum is the sum over all words x : Fin (n + t) → Fin q of the excess embedding count q_ary_subsequence_num_embeddings q n (n + t) y x - r.
-/

/-- Hinge sum W_r(y) of excess embedding counts of a length-n word y into words of length n+t. -/
def qary_multiple_deletion_hinge (t q n r : ℕ) (y : Fin n → Fin q) : ℕ := ∑ x : Fin (n + t) → Fin q, (q_ary_subsequence_num_embeddings q n (n + t) y x - r)
