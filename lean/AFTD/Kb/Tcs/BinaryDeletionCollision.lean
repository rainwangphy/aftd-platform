import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryDeletionNumEmbeddings

/-!
# binary_deletion_collision

Topic: information   Node: aa29da7151cc

Provenance: formalization of a published result. Source: arXiv:2611.01064: Maximal input entropy for binary two-deletion and two-insertion channels

For natural numbers k and n and a binary word w of length n, binary_deletion_collision k n w is the sum over all binary words u of length n - k of the square of binary_deletion_num_embeddings k n u w.
-/

/-- The k-deletion collision sum of a binary word w of length n. -/
def binary_deletion_collision (k n : ℕ) (w : Fin n → Bool) : ℕ := ∑ u : Fin (n - k) → Bool, (binary_deletion_num_embeddings k n u w) ^ 2
