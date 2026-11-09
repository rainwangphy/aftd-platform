import AFTD.Prelude
import AFTD.Kb.Tcs.DfaResetThreshold
import AFTD.Kb.Tcs.DfaProd
import AFTD.Kb.Tcs.DfaSubsetResetThreshold
import AFTD.Kb.Tcs.DfaProdIsSynchronizingOfSubsetSynchronizing
import AFTD.Kb.Tcs.DfaIsSubsetSynchronizing
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_prod_subset_sync_two_stage_bound

Topic: automata   Node: 3b4cf5ffe85c

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7

For any synchronizing word `w₁` of `A₁`, the reset threshold of the direct product `dfa_prod A₁ A₂` is at most the length of `w₁` plus the subset reset threshold of `Set.range (fun q => A₂.evalFrom q w₁)` in `A₂`.
-/

/-- The reset threshold of a direct product is bounded above by the two-stage subset synchronization length using any synchronizing word of A₁. -/
theorem dfa_prod_subset_sync_two_stage_bound {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) (w₁ : List α) (hw₁ : dfa_is_synchronizing A₁ w₁) : dfa_reset_threshold (dfa_prod A₁ A₂) ≤ (w₁.length : WithTop ℕ) + dfa_subset_reset_threshold A₂ (Set.range (fun q : σ₂ => A₂.evalFrom q w₁)) := by
  dsimp [dfa_subset_reset_threshold]
  by_cases h : ((fun w : List α => (w.length : WithTop ℕ)) '' {w | dfa_is_subset_synchronizing A₂ (Set.range fun q => A₂.evalFrom q w₁) w}).Nonempty
  · obtain ⟨v, hv, heq⟩ := csInf_mem h
    rw [← heq, ← Nat.cast_add, ← List.length_append]
    dsimp [dfa_reset_threshold]
    apply sInf_le
    exact Set.mem_image_of_mem _ (dfa_prod_is_synchronizing_of_subset_synchronizing A₁ A₂ w₁ v hw₁ hv)
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, WithTop.sInf_empty, WithTop.add_top]
    exact le_top
