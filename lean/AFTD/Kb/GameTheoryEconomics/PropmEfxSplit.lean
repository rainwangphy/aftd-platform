import AFTD.Prelude

/-!
# propm_efx_split

Topic: fair_division   Node: b78502058422

For one nonnegative additive valuation, every finite set of items has an EFX split: each side minus any one of its items is worth at most the other side.
-/

/-- EFX split for one additive nonnegative valuation: a split `T = X ⊔ (T \ X)` in which each side, minus any one of its items, is worth at most the other side. -/
lemma propm_efx_split {m : ℕ} (T : Finset (Fin m)) (v : Fin m → ℝ) (hv : ∀ x, 0 ≤ v x) :
    ∃ X ⊆ T, (∀ g ∈ X, 2 * ∑ x ∈ X, v x - ∑ x ∈ T, v x ≤ v g) ∧
      (∀ g ∈ T \ X, ∑ x ∈ T, v x - 2 * ∑ x ∈ X, v x ≤ v g) := by
  classical
  set P := T.filter (fun x => 0 < v x) with hP
  have hPT : P ⊆ T := Finset.filter_subset _ _
  have hsumP : ∑ x ∈ P, v x = ∑ x ∈ T, v x := by
    rw [hP, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rfl
    · exact (le_antisymm (not_lt.mp h) (hv x)).symm
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image P.powerset
    (fun S => |2 * ∑ x ∈ S, v x - ∑ x ∈ P, v x|) ⟨∅, Finset.empty_mem_powerset _⟩
  have key : ∃ A ⊆ P, ∑ x ∈ P, v x ≤ 2 * ∑ x ∈ A, v x ∧
      ∀ S' ⊆ P, |2 * ∑ x ∈ A, v x - ∑ x ∈ P, v x| ≤ |2 * ∑ x ∈ S', v x - ∑ x ∈ P, v x| := by
    rw [Finset.mem_powerset] at hS
    by_cases h : ∑ x ∈ P, v x ≤ 2 * ∑ x ∈ S, v x
    · exact ⟨S, hS, h, fun S' hS' => hmin S' (Finset.mem_powerset.mpr hS')⟩
    · have hc : ∑ x ∈ P \ S, v x = ∑ x ∈ P, v x - ∑ x ∈ S, v x := by
        rw [← Finset.sum_sdiff hS]; ring
      refine ⟨P \ S, Finset.sdiff_subset, by rw [hc]; linarith, fun S' hS' => ?_⟩
      have h1 := hmin S' (Finset.mem_powerset.mpr hS')
      have h2 : |2 * (∑ x ∈ P, v x - ∑ x ∈ S, v x) - ∑ x ∈ P, v x| =
          |2 * ∑ x ∈ S, v x - ∑ x ∈ P, v x| := by
        rw [← abs_neg]; ring_nf
      rw [hc, h2]; exact h1
  obtain ⟨A, hAP, hA, hAmin⟩ := key
  refine ⟨A, hAP.trans hPT, fun g hg => ?_, fun g _ => ?_⟩
  · have hgpos : 0 < v g := (Finset.mem_filter.mp (hAP hg)).2
    have h1 := hAmin (A.erase g) ((Finset.erase_subset _ _).trans hAP)
    rw [Finset.sum_erase_eq_sub hg] at h1
    rw [← hsumP]
    rcases abs_cases (2 * ∑ x ∈ A, v x - ∑ x ∈ P, v x) with ⟨h2, _⟩ | ⟨_, h2⟩ <;>
      rcases abs_cases (2 * (∑ x ∈ A, v x - v g) - ∑ x ∈ P, v x) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
      linarith
  · rw [← hsumP]; linarith [hv g]
