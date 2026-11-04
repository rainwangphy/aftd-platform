import AFTD.Prelude
import AFTD.Kb.Tcs.TwoDeletionNumEmbeddings

/-!
# two_insertion_collision

Topic: information   Node: fc7e7f5fbfe0

Provenance: formalization of a published result. Source: arXiv:2611.01064, Section 2

For a binary word w of length m + 2, two_insertion_collision m w is the sum over all binary words u of length m of the square of two_deletion_num_embeddings m u w.
-/

/-- Sum of squares of two-insertion (two-deletion) embedding counts over subwords of length m. -/
def two_insertion_collision (m : ℕ) (w : Fin (m + 2) → Bool) : ℕ := ∑ u : Fin m → Bool, (two_deletion_num_embeddings m u w) ^ 2
