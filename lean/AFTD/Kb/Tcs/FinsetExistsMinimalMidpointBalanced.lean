import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetIsMidpointBalanced

/-!
# finset_exists_minimal_midpoint_balanced

Topic: combinatorics   Node: 7c5b06330d61

Provenance: helper lemma. step towards finset_midpoint_balanced_exists_nonzero_minor

Every midpoint-balanced finite set B contains an inclusion-minimal midpoint-balanced subset B₀.
-/

/-- Every midpoint-balanced finite set B contains an inclusion-minimal midpoint-balanced subset B₀. -/
theorem finset_exists_minimal_midpoint_balanced {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (B : Finset G) (hB : finset_is_midpoint_balanced B) :
    ∃ B₀ ⊆ B, finset_is_midpoint_balanced B₀ ∧
      ∀ A ⊆ B₀, finset_is_midpoint_balanced A → A = B₀ := by
  classical
  let s := B.powerset.filter finset_is_midpoint_balanced
  have hs : B ∈ s := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_rfl, hB⟩
  obtain ⟨B₀, hB₀s, hmin⟩ := Finset.exists_min_image s Finset.card ⟨B, hs⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hB₀s
  refine ⟨B₀, hB₀s.1, hB₀s.2, fun A hAB₀ hA => ?_⟩
  have hAs : A ∈ s := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hAB₀.trans hB₀s.1, hA⟩
  exact Finset.eq_of_subset_of_card_le hAB₀ (hmin A hAs)
