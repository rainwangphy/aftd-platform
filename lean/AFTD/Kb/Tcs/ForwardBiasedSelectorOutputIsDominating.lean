import AFTD.Prelude
import AFTD.Kb.Tcs.IsDominatingDistribution
import AFTD.Kb.Tcs.IsForwardBiasedOptimal
import AFTD.Kb.Tcs.IsForwardBiasedSelectorOutput

/-!
# forward_biased_selector_output_is_dominating

Topic: online_algorithms   Node: 3b0d80600670

Provenance: helper lemma. arXiv:2610.40824 Proposition 7

The forward-biased selector output μ is always a dominating distribution.
-/

/-- The forward-biased selector output is dominating. -/
theorem forward_biased_selector_output_is_dominating {n : ℕ} {C : Finset (Fin n)}
    {α : Fin n → Fin n → ℝ} {e : Fin n} {μ : Fin n → ℝ}
    (h : is_forward_biased_selector_output C α e μ) :
    is_dominating_distribution C α μ := by
  exact h.1.1
