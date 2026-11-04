import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SweepCandidateBound

/-!
# sweep_candidate_bound_last

Topic: combinatorial_games   Node: c3c8d362c351

Provenance: helper lemma. arXiv:2611.01281 Section 5

For all natural numbers M and N, the sweep candidate bound satisfies sweep_candidate_bound M N (M - 2) (N - 1) = ∅.
-/

/-- The candidate set bound at the final sweep step (M-2, N-1) is empty. -/
theorem sweep_candidate_bound_last (M N : ℕ) :
    sweep_candidate_bound M N (M - 2) (N - 1) = ∅ := by
  ext p
  simp [sweep_candidate_bound]
  omega
