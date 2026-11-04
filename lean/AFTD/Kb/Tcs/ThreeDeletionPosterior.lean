import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeDeletionNumEmbeddings

/-!
# three_deletion_posterior

Topic: information   Node: 6fc801e75cd8

Provenance: formalization of a published result. Source: arXiv:2611.01064 Lemma 2.1

For a natural number n, a binary word w : Fin n → Bool, and a binary word y : Fin (n + 3) → Bool, three_deletion_posterior n w y is the real number defined by ((three_deletion_num_embeddings n w y : ℝ) / (8 * ((Nat.choose (n + 3) 3 : ℕ) : ℝ))).
-/

/-- Posterior distribution on transmitted words under three uniform deletions with uniform prior, valued in ℝ. -/
noncomputable def three_deletion_posterior (n : ℕ) (w : Fin n → Bool) (y : Fin (n + 3) → Bool) : ℝ := (three_deletion_num_embeddings n w y : ℝ) / (8 * ((n + 3).choose 3 : ℝ))
