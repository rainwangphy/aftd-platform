import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialCoeff

/-!
# petrial_log_concave

Topic: combinatorics   Node: 256098003780

Provenance: formalization of a published result. Source: arXiv:2611.07503, Section 2

A simple graph G on a finite type V with decidable equality and decidable adjacency has a log-concave partial Petrial polynomial if for every k : ℕ, whenever there exists i < k such that petrial_coeff G i ≠ 0 and there exists j > k such that petrial_coeff G j ≠ 0, we have petrial_coeff G (k - 1) * petrial_coeff G (k + 1) ≤ (petrial_coeff G k) ^ 2.
-/

/-- Log-concavity of the nonzero coefficient sequence of the partial Petrial polynomial. -/
def petrial_log_concave {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := ∀ k : ℕ, (∃ i < k, petrial_coeff G i ≠ 0) → (∃ j > k, petrial_coeff G j ≠ 0) →
    petrial_coeff G (k - 1) * petrial_coeff G (k + 1) ≤ petrial_coeff G k ^ 2
