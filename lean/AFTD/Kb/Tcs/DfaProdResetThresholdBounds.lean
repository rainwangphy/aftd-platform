import AFTD.Prelude
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaProdIsSynchronizingIff
import AFTD.Kb.Tcs.DfaProdIsSynchronizingAppend
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_prod_reset_threshold_bounds

Topic: automata   Node: ee6dc5f6abee

Provenance: formalization of a published result. Source: arXiv:2611.09136 Proposition 3.4

For any two deterministic finite automata `A₁` and `A₂` over the same alphabet, the reset threshold of their direct product satisfies `max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂) ≤ dfa_reset_threshold (dfa_prod A₁ A₂)` and `dfa_reset_threshold (dfa_prod A₁ A₂) ≤ dfa_reset_threshold A₁ + dfa_reset_threshold A₂`.
-/

/-- Reset threshold bounds for direct products of DFAs: max(rt(A₁), rt(A₂)) ≤ rt(A₁ × A₂) ≤ rt(A₁) + rt(A₂). -/
theorem dfa_prod_reset_threshold_bounds {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) : max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂) ≤ dfa_reset_threshold (dfa_prod A₁ A₂) ∧ dfa_reset_threshold (dfa_prod A₁ A₂) ≤ dfa_reset_threshold A₁ + dfa_reset_threshold A₂ := by
  constructor
  · rw [max_le_iff]
    dsimp [dfa_reset_threshold]
    constructor
    · apply sInf_le_sInf
      rintro - ⟨w, hw, rfl⟩
      exact ⟨w, (dfa_prod_is_synchronizing_iff A₁ A₂ w).mp hw |>.1, rfl⟩
    · apply sInf_le_sInf
      rintro - ⟨w, hw, rfl⟩
      exact ⟨w, (dfa_prod_is_synchronizing_iff A₁ A₂ w).mp hw |>.2, rfl⟩
  · by_cases h₁ : ((fun w : List α => (w.length : WithTop ℕ)) '' {w | dfa_is_synchronizing A₁ w}).Nonempty
    · by_cases h₂ : ((fun w : List α => (w.length : WithTop ℕ)) '' {w | dfa_is_synchronizing A₂ w}).Nonempty
      · obtain ⟨w₁, hw₁, heq₁⟩ := csInf_mem h₁
        obtain ⟨w₂, hw₂, heq₂⟩ := csInf_mem h₂
        have hsync : dfa_is_synchronizing (dfa_prod A₁ A₂) (w₁ ++ w₂) :=
          dfa_prod_is_synchronizing_append A₁ A₂ w₁ w₂ hw₁ hw₂
        dsimp [dfa_reset_threshold]
        dsimp [dfa_reset_threshold] at heq₁ heq₂
        rw [← heq₁, ← heq₂]
        rw [← Nat.cast_add, ← List.length_append]
        apply sInf_le
        exact ⟨w₁ ++ w₂, hsync, rfl⟩
      · rw [Set.not_nonempty_iff_eq_empty] at h₂
        dsimp [dfa_reset_threshold]
        rw [h₂, WithTop.sInf_empty, WithTop.add_top]
        exact le_top
    · rw [Set.not_nonempty_iff_eq_empty] at h₁
      dsimp [dfa_reset_threshold]
      rw [h₁, WithTop.sInf_empty, WithTop.top_add]
      exact le_top
