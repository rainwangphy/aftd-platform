import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# submodular_universal_family

Topic: submodular   Node: 70f20b89f152

Provenance: formalization of a published result. Source: arXiv:2611.23637 Sec. 1.1, Theorem 1.1

A finite family of subsets F of {0, ..., n-1} is a gamma-universal family for submodular maximization if for every non-negative submodular function f, there exists some set R in F such that f(R) >= gamma * f(S) for all subsets S.
-/

/-- A family F of subsets is a gamma-universal family for submodular maximization if every non-negative submodular function has its maximum over F at least gamma times its unconstrained maximum. -/
def submodular_universal_family {n : ℕ} (F : Finset (Finset (Fin n))) (γ : ℝ) : Prop :=
  ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → is_submodular f →
    ∃ R ∈ F, ∀ S : Finset (Fin n), γ * f S ≤ f R
