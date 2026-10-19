import AFTD.Prelude

/-!
# DiscreteDist

Topic: online_algorithms   Node: 10496843ce97

Provenance: formalization of a published result. Source: arXiv:2610.13775, Sec. 2.1

A discrete probability distribution with finite support on non-negative real values, defined by a finite support set, non-negative probabilities summing to 1, and non-negative support elements.
-/

/-- A discrete probability distribution with finite support on non-negative real numbers. -/
structure DiscreteDist where
  support : Finset ℝ
  prob : ℝ → ℝ
  prob_nonneg : ∀ v ∈ support, 0 ≤ prob v
  sum_prob_one : ∑ v ∈ support, prob v = 1
  val_nonneg : ∀ v ∈ support, 0 ≤ v
