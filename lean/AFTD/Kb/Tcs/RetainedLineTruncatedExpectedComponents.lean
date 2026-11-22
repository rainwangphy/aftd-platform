import AFTD.Prelude
import AFTD.Kb.Tcs.RetainedLineTruncate

/-!
# retained_line_truncated_expected_components

Topic: algorithms   Node: 96641b6e7336

Provenance: helper lemma. step towards retained_line_msf_fixed_q_limit

The expected number of connected components of the length-≤d truncation of the random graph on n line vertices where each edge is retained independently with probability q.
-/

/-- Expected number of components of the length-`d` truncation of the `q`-random graph on `n` line vertices. -/
noncomputable def retained_line_truncated_expected_components (n d : ℕ) (q : ℝ) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n),
    q ^ G.edgeFinset.card * (1 - q) ^ (Nat.choose n 2 - G.edgeFinset.card) *
      (Nat.card (retained_line_truncate G d).ConnectedComponent : ℝ)
