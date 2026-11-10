import AFTD.Prelude
import AFTD.Kb.Tcs.DfaProdAttainsLowerBound
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProdResetThresholdBounds
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaProdIsSynchronizingIff
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_prod_attains_lower_bound_of_subsingleton

Topic: automata   Node: 51c67a7d8b85

Provenance: formalization of a published result. Source: arXiv:2611.09136 Proposition 3.13

Proposition 3.13 of arXiv:2611.09136: For any two DFAs `A₁` and `A₂` over a subsingleton (unary) alphabet, their direct product always attains the lower bound `max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂)` on its reset threshold.
-/

lemma dfa_prod_attains_lower_bound_of_subsingleton_append_right {α σ : Type*} (A : DFA α σ) (w v : List α)
    (hw : dfa_is_synchronizing A w) : dfa_is_synchronizing A (w ++ v) := by
  intro q₁ q₂
  simp only [DFA.evalFrom_of_append]
  rw [hw q₁ q₂]

lemma dfa_prod_attains_lower_bound_of_subsingleton_eq_append_drop {α : Type*} [Subsingleton α] (l₁ l₂ : List α)
    (h : l₁.length ≤ l₂.length) : l₂ = l₁ ++ l₂.drop l₁.length := by
  have htake : l₂.take l₁.length = l₁ := by
    refine List.ext_get ?_ (fun n h₁ h₂ => Subsingleton.elim _ _)
    simp [List.length_take, h]
  conv_lhs => rw [← List.take_append_drop l₁.length l₂]
  rw [htake]

lemma dfa_prod_attains_lower_bound_of_subsingleton_sync_of_le {α σ : Type*} [Subsingleton α] (A : DFA α σ)
    (l₁ l₂ : List α) (hw : dfa_is_synchronizing A l₁) (h : l₁.length ≤ l₂.length) :
    dfa_is_synchronizing A l₂ := by
  rw [dfa_prod_attains_lower_bound_of_subsingleton_eq_append_drop l₁ l₂ h]
  exact dfa_prod_attains_lower_bound_of_subsingleton_append_right A l₁ (l₂.drop l₁.length) hw

/-- Direct products of DFAs over a subsingleton alphabet always attain the lower bound on the reset threshold. -/
theorem dfa_prod_attains_lower_bound_of_subsingleton {α σ₁ σ₂ : Type*} [Subsingleton α] (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) : dfa_prod_attains_lower_bound A₁ A₂ := by
  dsimp [dfa_prod_attains_lower_bound]
  have h_bound := (dfa_prod_reset_threshold_bounds A₁ A₂).1
  by_cases h₁ : dfa_reset_threshold A₁ = ⊤
  · rw [h₁, max_top_left] at h_bound ⊢
    exact top_le_iff.mp h_bound
  by_cases h₂ : dfa_reset_threshold A₂ = ⊤
  · rw [h₂, max_top_right] at h_bound ⊢
    exact top_le_iff.mp h_bound
  have h_ne₁ : ((fun w : List α => (w.length : WithTop ℕ)) '' {w | dfa_is_synchronizing A₁ w}).Nonempty := by
    dsimp [dfa_reset_threshold] at h₁
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    rw [he, WithTop.sInf_empty] at h₁
    exact h₁ rfl
  have h_ne₂ : ((fun w : List α => (w.length : WithTop ℕ)) '' {w | dfa_is_synchronizing A₂ w}).Nonempty := by
    dsimp [dfa_reset_threshold] at h₂
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    rw [he, WithTop.sInf_empty] at h₂
    exact h₂ rfl
  obtain ⟨w₁, hw₁, heq₁⟩ := csInf_mem h_ne₁
  obtain ⟨w₂, hw₂, heq₂⟩ := csInf_mem h_ne₂
  dsimp only at heq₁ heq₂
  apply le_antisymm _ h_bound
  rcases le_total w₁.length w₂.length with hle | hle
  · have hsync₁ : dfa_is_synchronizing A₁ w₂ :=
      dfa_prod_attains_lower_bound_of_subsingleton_sync_of_le A₁ w₁ w₂ hw₁ hle
    have hprod : dfa_is_synchronizing (dfa_prod A₁ A₂) w₂ :=
      (dfa_prod_is_synchronizing_iff A₁ A₂ w₂).mpr ⟨hsync₁, hw₂⟩
    have h_le : dfa_reset_threshold (dfa_prod A₁ A₂) ≤ (w₂.length : WithTop ℕ) := by
      dsimp [dfa_reset_threshold]
      exact sInf_le ⟨w₂, hprod, rfl⟩
    have hmax : (w₂.length : WithTop ℕ) ≤ max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂) := by
      rw [heq₂]
      exact le_max_right _ _
    exact le_trans h_le hmax
  · have hsync₂ : dfa_is_synchronizing A₂ w₁ :=
      dfa_prod_attains_lower_bound_of_subsingleton_sync_of_le A₂ w₂ w₁ hw₂ hle
    have hprod : dfa_is_synchronizing (dfa_prod A₁ A₂) w₁ :=
      (dfa_prod_is_synchronizing_iff A₁ A₂ w₁).mpr ⟨hw₁, hsync₂⟩
    have h_le : dfa_reset_threshold (dfa_prod A₁ A₂) ≤ (w₁.length : WithTop ℕ) := by
      dsimp [dfa_reset_threshold]
      exact sInf_le ⟨w₁, hprod, rfl⟩
    have hmax : (w₁.length : WithTop ℕ) ≤ max (dfa_reset_threshold A₁) (dfa_reset_threshold A₂) := by
      rw [heq₁]
      exact le_max_left _ _
    exact le_trans h_le hmax
