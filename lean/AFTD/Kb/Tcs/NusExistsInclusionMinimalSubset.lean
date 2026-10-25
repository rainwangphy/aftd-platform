import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums
import AFTD.Kb.Tcs.FinsetHasNoUniqueSumsDecidable

/-!
# nus_exists_inclusion_minimal_subset

Topic: combinatorics   Node: f71ebae30e58

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

Every finite set with no unique sums contains an inclusion-minimal one: there is a subset B of A that has no unique sums and none of whose proper subsets has no unique sums.
-/

/-- Every NUS set contains an inclusion-minimal NUS subset (opening line of Section 2 of Hou-Yang). -/
theorem nus_exists_inclusion_minimal_subset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (hA : finset_has_no_unique_sums A) :
    ∃ B : Finset G, B ⊆ A ∧ finset_has_no_unique_sums B ∧
      ∀ C : Finset G, C ⊂ B → ¬ finset_has_no_unique_sums C := by
  classical
  let S := A.powerset.filter (fun B => finset_has_no_unique_sums B)
  have hS : A ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset_self A, hA⟩
  obtain ⟨B, hB_mem, hB_min⟩ := Finset.exists_min_image S Finset.card ⟨A, hS⟩
  rw [Finset.mem_filter] at hB_mem
  rcases hB_mem with ⟨hBA, hB_nus⟩
  rw [Finset.mem_powerset] at hBA
  refine ⟨B, hBA, hB_nus, fun C hCB hC_nus => ?_⟩
  have hCA : C ⊆ A := hCB.1.trans hBA
  have hCS : C ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hCA, hC_nus⟩
  have h_le := hB_min C hCS
  have h_lt := Finset.card_lt_card hCB
  omega
