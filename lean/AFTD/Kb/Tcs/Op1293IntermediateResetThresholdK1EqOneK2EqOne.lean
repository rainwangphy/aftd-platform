import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.Op1293ProductResetThresholdUpperBoundAttained
import AFTD.Kb.Tcs.Op1293ProductResetThresholdLowerBoundAttained

/-!
# op_1293_intermediate_reset_threshold_k1_eq_one_k2_eq_one

Topic: automata   Node: e8c2e9215ce1

Provenance: helper lemma. arXiv:2611.09136 Sec. 7, open question 2

For every finite alphabet α with at least two symbols and k ∈ {1, 2}, there exist finite state types σ₁, σ₂ and synchronizable DFAs A₁ : DFA α σ₁ and A₂ : DFA α σ₂ with dfa_reset_threshold A₁ = 1 and dfa_reset_threshold A₂ = 1 such that the reset threshold of their direct product is k.
-/

/-- Attainability of intermediate reset thresholds for the base case k₁ = 1, k₂ = 1. -/
theorem op_1293_intermediate_reset_threshold_k1_eq_one_k2_eq_one (α : Type*) [Fintype α] (hα : 2 ≤ Fintype.card α) (k : ℕ) (hk : k = 1 ∨ k = 2) : ∃ (σ₁ σ₂ : Type) (_ : Fintype σ₁) (_ : Fintype σ₂) (A₁ : DFA α σ₁) (A₂ : DFA α σ₂), dfa_is_synchronizable A₁ ∧ dfa_is_synchronizable A₂ ∧ dfa_reset_threshold A₁ = 1 ∧ dfa_reset_threshold A₂ = 1 ∧ dfa_reset_threshold (dfa_prod A₁ A₂) = ↑k := by
  rcases hk with rfl | rfl
  · have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨σ₁, σ₂, hσ₁, hσ₂, A₁, A₂, h1, h2, h3, h4, h5⟩ :=
      op_1293_product_reset_threshold_lower_bound_attained α 1 1 (by omega) (by omega)
    exact ⟨σ₁, σ₂, hσ₁, hσ₂, A₁, A₂, h1, h2, h3, h4, h5⟩
  · obtain ⟨σ₁, σ₂, hσ₁, hσ₂, A₁, A₂, h1, h2, h3, h4, h5⟩ :=
      op_1293_product_reset_threshold_upper_bound_attained α hα 1 1 (by omega) (by omega)
    exact ⟨σ₁, σ₂, hσ₁, hσ₂, A₁, A₂, h1, h2, h3, h4, h5⟩
