import AFTD.Prelude
import AFTD.Kb.Tcs.QaryDeletionNumEmbeddings

/-!
# qary_deletion_collision

Topic: information   Node: 8493b6ecb356

Provenance: formalization of a published result. Source: arXiv:2611.01064

For natural numbers q, k, and n and a word w of length n over an alphabet of size q, qary_deletion_collision q k n w is the sum over all words u of length n - k over Fin q of the square of qary_deletion_num_embeddings q k n u w.
-/

/-- Sum of squared embedding counts over all subwords of length n - k. -/
def qary_deletion_collision (q k n : ℕ) (w : Fin n → Fin q) : ℕ := ∑ u : Fin (n - k) → Fin q, (qary_deletion_num_embeddings q k n u w) ^ 2
