import AFTD.Prelude
import AFTD.Kb.Tcs.IsDominatingDistribution
import AFTD.Kb.Tcs.IsForwardBiasedOptimal

/-!
# is_forward_biased_selector_output

Topic: online_algorithms   Node: 26334f1844b3

Provenance: formalization of a published result. Source: arXiv:2610.40824 Definition 6

A distribution μ is the forward-biased selector output for cache C, hitting probabilities α, and target page e if μ is an optimal solution to the forward-biased linear program and every other optimal solution ν is strictly smaller than μ in lexicographical order Pi.Lex (· < ·) (· < ·).
-/

/-- The lexicographically largest optimal solution to the forward-biased LP. -/
def is_forward_biased_selector_output {n : ℕ} (C : Finset (Fin n))
    (α : Fin n → Fin n → ℝ) (e : Fin n) (μ : Fin n → ℝ) : Prop := is_forward_biased_optimal C α e μ ∧
  ∀ ν, is_forward_biased_optimal C α e ν → (ν = μ ∨ Pi.Lex (· < ·) (· < ·) ν μ)
