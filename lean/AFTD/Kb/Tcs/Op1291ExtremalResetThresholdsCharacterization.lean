import AFTD.Prelude
import AFTD.Kb.Tcs.DfaProdAttainsLowerBound
import AFTD.Kb.Tcs.DfaProdAttainsUpperBound
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaIsSynchronizing
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaProdIsSynchronizingIff
import AFTD.Kb.Tcs.DfaProdIsSynchronizingAppend
import AFTD.Kb.Tcs.DfaProdResetThresholdBounds

/-!
# op_1291_extremal_reset_thresholds_characterization

Topic: automata   Node: 0f9f31f4ebaa

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7, open question 1

Open Problem OP-1291: For any synchronizable DFAs `A₁` and `A₂` over a common alphabet, the direct product attains the lower bound `max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)` if and only if there exists a word synchronizing both `A₁` and `A₂` of length at most `max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)`, and attains the upper bound `dfa_reset_threshold A₁ + dfa_reset_threshold A₂` if and only if every word synchronizing both `A₁` and `A₂` has length at least `dfa_reset_threshold A₁ + dfa_reset_threshold A₂`.
-/

/-- Characterization of when the direct product of two DFAs attains the lower and upper reset threshold bounds of Proposition 3.4. -/
theorem op_1291_extremal_reset_thresholds_characterization {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (h₁ : dfa_is_synchronizable A₁) (h₂ : dfa_is_synchronizable A₂) : (dfa_prod_attains_lower_bound A₁ A₂ ↔ ∃ w : List α, dfa_is_synchronizing A₁ w ∧ dfa_is_synchronizing A₂ w ∧ (w.length : WithTop ℕ) ≤ max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)) ∧ (dfa_prod_attains_upper_bound A₁ A₂ ↔ ∀ w : List α, dfa_is_synchronizing A₁ w → dfa_is_synchronizing A₂ w → dfa_reset_threshold A₁ + dfa_reset_threshold A₂ ≤ (w.length : WithTop ℕ)) := by
  constructor
  · constructor
    · intro h
      obtain ⟨w₁, hw₁⟩ := h₁
      obtain ⟨w₂, hw₂⟩ := h₂
      have h_prod_sync : dfa_is_synchronizing (dfa_prod A₁ A₂) (w₁ ++ w₂) :=
        dfa_prod_is_synchronizing_append A₁ A₂ w₁ w₂ hw₁ hw₂
      have h_nonempty : ((fun w : List α => (w.length : WithTop ℕ)) ''
          {w | dfa_is_synchronizing (dfa_prod A₁ A₂) w}).Nonempty :=
        ⟨↑(w₁ ++ w₂).length, ⟨w₁ ++ w₂, h_prod_sync, rfl⟩⟩
      have h_mem := csInf_mem h_nonempty
      obtain ⟨w, hw, heq⟩ := h_mem
      have hw' : dfa_is_synchronizing A₁ w ∧ dfa_is_synchronizing A₂ w :=
        (dfa_prod_is_synchronizing_iff A₁ A₂ w).mp hw
      refine ⟨w, hw'.1, hw'.2, ?_⟩
      change dfa_reset_threshold (dfa_prod A₁ A₂) = max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂) at h
      change (w.length : WithTop ℕ) = dfa_reset_threshold (dfa_prod A₁ A₂) at heq
      rw [heq, h]
    · intro ⟨w, hw₁, hw₂, hw_le⟩
      have h_sync : dfa_is_synchronizing (dfa_prod A₁ A₂) w :=
        (dfa_prod_is_synchronizing_iff A₁ A₂ w).mpr ⟨hw₁, hw₂⟩
      have h_le : dfa_reset_threshold (dfa_prod A₁ A₂) ≤ (w.length : WithTop ℕ) := by
        dsimp [dfa_reset_threshold]
        exact sInf_le ⟨w, h_sync, rfl⟩
      have h_trans : dfa_reset_threshold (dfa_prod A₁ A₂) ≤ max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂) :=
        le_trans h_le hw_le
      have h_bound := (dfa_prod_reset_threshold_bounds A₁ A₂).1
      exact le_antisymm h_trans h_bound
  · dsimp [dfa_prod_attains_upper_bound, dfa_reset_threshold]
    have h_le := (dfa_prod_reset_threshold_bounds A₁ A₂).2
    dsimp [dfa_reset_threshold] at h_le
    constructor
    · intro h w hw₁ hw₂
      rw [← h]
      apply sInf_le
      exact ⟨w, (dfa_prod_is_synchronizing_iff A₁ A₂ w).mpr ⟨hw₁, hw₂⟩, rfl⟩
    · intro h
      apply le_antisymm h_le
      rw [le_sInf_iff]
      rintro - ⟨w, hw, rfl⟩
      have hw' : dfa_is_synchronizing A₁ w ∧ dfa_is_synchronizing A₂ w :=
        (dfa_prod_is_synchronizing_iff A₁ A₂ w).mp hw
      exact h w hw'.1 hw'.2
