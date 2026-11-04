import AFTD.Prelude
import AFTD.Kb.Tcs.TwoDeletionPosterior
import AFTD.Kb.Tcs.TwoDeletionNumEmbeddings

/-!
# two_deletion_posterior_sum_two

Topic: information   Node: 060a2057b4d2

Provenance: helper lemma. arXiv:2611.01064, Lemma 2.1

For every received binary word w of length 2, the posterior distribution two_deletion_posterior 2 w over words of length 4 sums to 1.
-/

/-- For any received binary word of length 2, the two-deletion posterior distribution sums to 1. -/
theorem two_deletion_posterior_sum_two (w : Fin 2 → Bool) : ∑ y : Fin 4 → Bool, two_deletion_posterior 2 w y = 1 := by
  -- Double counting / direct evaluation: for every w the total number of
  -- embeddings over all transmitted words y is 4 * (4 choose 2) = 24.
  have h : ∀ w : Fin 2 → Bool, ∑ y : Fin 4 → Bool, two_deletion_num_embeddings 2 w y = 24 := by
    decide
  have hw := h w
  simp only [two_deletion_posterior]
  rw [show Nat.choose 4 2 = 6 from by decide]
  norm_num
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [hw]
  norm_num
