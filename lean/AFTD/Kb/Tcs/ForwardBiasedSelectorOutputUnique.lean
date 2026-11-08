import AFTD.Prelude
import AFTD.Kb.Tcs.IsForwardBiasedSelectorOutput
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsForwardBiasedOptimal

/-!
# forward_biased_selector_output_unique

Topic: online_algorithms   Node: 155de2277538

Provenance: helper lemma. arXiv:2610.40824 Proposition 7

For any cache C, hitting probabilities α, and target page e, if μ₁ and μ₂ both satisfy is_forward_biased_selector_output C α e, then μ₁ = μ₂.
-/

/-- Uniqueness of the forward-biased selector output. -/
theorem forward_biased_selector_output_unique {n : ℕ} {C : Finset (Fin n)}
    {α : Fin n → Fin n → ℝ} {e : Fin n} {μ₁ μ₂ : Fin n → ℝ}
    (h₁ : is_forward_biased_selector_output C α e μ₁)
    (h₂ : is_forward_biased_selector_output C α e μ₂) :
    μ₁ = μ₂ := by
  obtain ⟨hopt₁, hmin₁⟩ := h₁
  obtain ⟨hopt₂, hmin₂⟩ := h₂
  rcases hmin₁ μ₂ hopt₂ with h | h
  · exact h.symm
  rcases hmin₂ μ₁ hopt₁ with h' | h'
  · exact h'
  · exfalso
    have hlt1 : toLex μ₁ < toLex μ₂ := h'
    have hlt2 : toLex μ₂ < toLex μ₁ := h
    exact lt_irrefl _ (hlt1.trans hlt2)
