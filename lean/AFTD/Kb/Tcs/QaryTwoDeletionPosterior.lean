import AFTD.Prelude
import AFTD.Kb.Tcs.QArySubsequenceNumEmbeddings

/-!
# qary_two_deletion_posterior

Topic: information   Node: 2a2ee1a95d95

Provenance: formalization of a published result. Source: arXiv:2611.01064, Lemma 2.1

For a received q-ary word y of length n, qary_two_deletion_posterior q n y x is the posterior probability of transmitting x of length n + 2 after two uniformly chosen deletions under a uniform prior, given by the number of subsequence embeddings of y in x divided by q^2 * Nat.choose (n + 2) 2.
-/

/-- Posterior probability of transmitting x given received word y after two deletions in a q-ary channel under uniform prior. -/
noncomputable def qary_two_deletion_posterior (q n : ℕ) (y : Fin n → Fin q) (x : Fin (n + 2) → Fin q) : ℝ := (q_ary_subsequence_num_embeddings q n (n + 2) y x : ℝ) / ((q : ℝ) ^ 2 * (Nat.choose (n + 2) 2 : ℝ))
