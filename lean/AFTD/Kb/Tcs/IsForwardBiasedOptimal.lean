import AFTD.Prelude
import AFTD.Kb.Tcs.IsDominatingDistribution

/-!
# is_forward_biased_optimal

Topic: online_algorithms   Node: 0ec0aeca4a85

Provenance: formalization of a published result. Source: arXiv:2610.40824 Definition 6, eq. (5)

A distribution μ is an optimal solution to the forward-biased linear program if μ is a dominating distribution supported on cache C and maximizes the mass μ e on the target page e among all dominating distributions on C.
-/

/-- A dominating distribution μ maximizing μ(e). -/
def is_forward_biased_optimal {n : ℕ} (C : Finset (Fin n))
    (α : Fin n → Fin n → ℝ) (e : Fin n) (μ : Fin n → ℝ) : Prop := is_dominating_distribution C α μ ∧
  ∀ ν, is_dominating_distribution C α ν → ν e ≤ μ e
