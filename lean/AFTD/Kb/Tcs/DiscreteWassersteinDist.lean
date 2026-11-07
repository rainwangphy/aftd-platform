import AFTD.Prelude

/-!
# discrete_wasserstein_dist

Topic: online_algorithms   Node: b20bdb622459

Provenance: formalization of a published result. Source: arXiv:2611.04275, Section 2.2, eq. (2.2)

The discrete Wasserstein-1 distance between two probability distributions on a pseudo metric space X with finite index sets I and J, probability weights p and q, and support points x : I → X and y : J → X, defined as the infimum of ∑_{i, j} γ(i, j) d(x_i, y_j) over all transport plans γ ≥ 0 with row sums p and column sums q.
-/

/-- Wasserstein-1 distance between two finitely indexed discrete distributions on a pseudo metric space. -/
noncomputable def discrete_wasserstein_dist {X : Type*} [PseudoMetricSpace X]
    {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (x : I → X) (q : J → ℝ) (y : J → X) : ℝ :=
  sInf {c : ℝ | ∃ γ : I → J → ℝ,
    (∀ i j, 0 ≤ γ i j) ∧
    (∀ i, ∑ j, γ i j = p i) ∧
    (∀ j, ∑ i, γ i j = q j) ∧
    c = ∑ i, ∑ j, γ i j * dist (x i) (y j)}
