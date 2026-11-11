import AFTD.Prelude
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings

/-!
# qary_two_deletion_hinge

Topic: information   Node: acee847bbadc

Provenance: original. Related work: OP-1499; arXiv:2611.01064

For integers q, n, and r, and a q-ary word y of length n, qary_two_deletion_hinge q n r y is the sum over all words x : Fin (n + 2) → Fin q of the thresholded excess embedding count max(e(y, x) - r, 0), computed via truncating natural subtraction.
-/

/-- Thresholded excess subsequence embedding sum W_r(y) over length n + 2 words. -/
def qary_two_deletion_hinge (q n r : ℕ) (y : Fin n → Fin q) : ℕ := ∑ x : Fin (n + 2) → Fin q, (q_ary_subsequence_num_embeddings q n (n + 2) y x - r)
