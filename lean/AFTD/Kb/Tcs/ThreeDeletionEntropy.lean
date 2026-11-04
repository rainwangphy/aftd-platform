import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeDeletionPosterior
import AFTD.Kb.Tcs.ShannonEntropy

/-!
# three_deletion_entropy

Topic: information   Node: 840c4169db2e

Provenance: formalization of a published result. Source: arXiv:2611.01064 Lemma 2.1

For a natural number n and a binary word w : Fin n → Bool, three_deletion_entropy n w is the real number defined as shannon_entropy (three_deletion_posterior n w) / Real.log 2.
-/

/-- Base-2 Shannon entropy of the three-deletion posterior distribution. -/
noncomputable def three_deletion_entropy (n : ℕ) (w : Fin n → Bool) : ℝ := shannon_entropy (three_deletion_posterior n w) / Real.log 2
