import AFTD.Prelude
import AFTD.Kb.Tcs.TwoDeletionNumEmbeddings

/-!
# two_deletion_posterior

Topic: information   Node: 99159d587a94

Provenance: formalization of a published result. Source: arXiv:2611.01064, Lemma 2.1

For a received binary word w of length n, two_deletion_posterior n w y is the posterior probability of transmitting y of length n + 2 after two uniformly chosen deletions under a uniform prior, equal to the number of embeddings divided by 4 * Nat.choose (n + 2) 2.
-/

/-- Posterior probability of transmitted word y given received word w after two deletions under uniform prior. -/
noncomputable def two_deletion_posterior (n : ℕ) (w : Fin n → Bool) (y : Fin (n + 2) → Bool) : ℝ := (two_deletion_num_embeddings n w y : ℝ) / (4 * Nat.choose (n + 2) 2)
