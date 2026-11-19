import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submodular_random_sample_guarantee

Topic: submodular   Node: 7a576f13d644

Provenance: formalization of a published result. Source: arXiv:2611.23637 Sec. 1.1, after Theorem 1.2

A sample R_1, ..., R_t of subsets of {0, ..., n-1} satisfies the gamma-approximation guarantee for submodular maximization if for every non-negative submodular function f, there exists an index i such that f(R_i) >= gamma * f(S) for all subsets S.
-/

/-- A sample of t subsets achieves the gamma-approximation guarantee for submodular maximization if every non-negative submodular function achieves at least gamma times its maximum on some set in the sample. -/
def submodular_random_sample_guarantee {n t : ℕ} (R : Fin t → Finset (Fin n)) (γ : ℝ) : Prop :=
  ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → is_submodular f →
    ∃ i : Fin t, ∀ S : Finset (Fin n), γ * f S ≤ f (R i)
