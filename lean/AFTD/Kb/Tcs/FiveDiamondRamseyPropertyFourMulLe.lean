import AFTD.Prelude
import AFTD.Kb.Tcs.PosetRamseyProperty
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.FiveDiamondRamseyPropertyIffSets
import AFTD.Kb.Tcs.FiveDiamondLevelColoring
import AFTD.Kb.Tcs.FiveDiamondLevelColoringIntervalCardLeThree

/-!
# five_diamond_ramsey_property_four_mul_le

Topic: combinatorics   Node: b94e5ff185d1

Provenance: helper lemma. step towards five_diamond_poset_ramsey_number_ge

If every k-colouring (k ≥ 1) of the subsets of Fin d contains a monochromatic induced copy of the 5-diamond DiamondPoset 5, then 4 * k ≤ d. Equivalently, the colouring A ↦ min (k-1) (|A| / 4) of the Boolean lattice on fewer than 4k points has no monochromatic induced 5-diamond.
-/

lemma five_diamond_ramsey_property_four_mul_le_antichain_card_le_three
    {α : Type*} [DecidableEq α] {X : Finset α} (hX : X.card ≤ 3)
    (𝒜 : Finset (Finset α)) (hsub : ∀ S ∈ 𝒜, S ⊆ X)
    (hanti : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ 3 := by
  let p := fun a => a ∈ X
  have hinj : Set.InjOn (Finset.subtype p) 𝒜 := by
    intro S hS T hT hST
    have h1 := Finset.subtype_map_of_mem (fun x hx => hsub S hS hx)
    have h2 := Finset.subtype_map_of_mem (fun x hx => hsub T hT hx)
    rw [← h1, ← h2, hST]
  have hcard : 𝒜.card = (𝒜.image (Finset.subtype p)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hantiB : IsAntichain (· ⊆ ·) ((𝒜.image (Finset.subtype p) : Finset (Finset (Subtype p))) : Set (Finset (Subtype p))) := by
    intro A hA B hB hne
    rw [Finset.mem_coe, Finset.mem_image] at hA hB
    obtain ⟨S, hS, rfl⟩ := hA
    obtain ⟨T, hT, rfl⟩ := hB
    intro hle
    have hST_ne : S ≠ T := by rintro rfl; exact hne rfl
    have hST_le : S ⊆ T := by
      intro x hx
      have hx_sub : (⟨x, hsub S hS hx⟩ : Subtype p) ∈ Finset.subtype p S := by
        rw [Finset.mem_subtype]; exact hx
      have := hle hx_sub
      rw [Finset.mem_subtype] at this
      exact this
    exact hanti (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hST_ne hST_le
  have hsperner := IsAntichain.sperner hantiB
  have hFcard : Fintype.card (Subtype p) = X.card := Fintype.card_coe X
  rw [hFcard] at hsperner
  have h3 : X.card.choose (X.card / 2) ≤ 3 := by
    interval_cases X.card <;> decide
  omega

lemma five_diamond_ramsey_property_four_mul_le_five_subsets
    {α : Type*} [DecidableEq α] (X : Finset α) (hX : X.card ≤ 3)
    (M : Fin 5 → Finset α) (hM : ∀ i : Fin 5, M i ⊆ X) :
    ∃ i i', i ≠ i' ∧ (M i ⊆ M i' ∨ M i' ⊆ M i) := by
  by_contra! h
  have hinj : Function.Injective M := by
    intro i j hij
    by_contra hne
    exact (h i j hne).1 (hij ▸ subset_rfl)
  let 𝒜 := Finset.image M Finset.univ
  have hcard : 𝒜.card = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : ∀ S ∈ 𝒜, S ⊆ X := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨i, -, rfl⟩ := hS
    exact hM i
  have hanti : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α)) := by
    intro A hA B hB hne hle
    rw [Finset.mem_coe, Finset.mem_image] at hA hB
    obtain ⟨i, -, rfl⟩ := hA
    obtain ⟨j, -, rfl⟩ := hB
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    exact (h i j hij).1 hle
  have := five_diamond_ramsey_property_four_mul_le_antichain_card_le_three hX 𝒜 hsub hanti
  omega

/-- Any d for which the k-colour 5-diamond Ramsey property holds is at least 4*k, by the colouring that only looks at |A| / 4, truncated at k - 1. -/
theorem five_diamond_ramsey_property_four_mul_le (k d : ℕ) (hk : 1 ≤ k)
    (hd : poset_ramsey_property (DiamondPoset 5) k d) : 4 * k ≤ d := by
  classical
  by_contra! h
  have hd_le : d ≤ 4 * k - 1 := by omega
  have hprop := (five_diamond_ramsey_property_iff_sets 5 k d).mp hd (five_diamond_level_coloring k d hk)
  obtain ⟨col, B, T, M, hcB, hcT, hcM, hBT, hBMT, hincomp⟩ := hprop
  have hcol_eq :
      five_diamond_level_coloring k d hk B =
        five_diamond_level_coloring k d hk T := by
    rw [hcB, hcT]
  have hcard : (T \ B).card ≤ 3 :=
    five_diamond_level_coloring_interval_card_le_three k d hk hd_le B T hBT hcol_eq
  have hDi_sub : ∀ i : Fin 5, M i \ B ⊆ T \ B := by
    intro i
    exact Finset.sdiff_subset_sdiff (hBMT i).2.1 (le_refl B)
  have hDinc : ∀ i i' : Fin 5, i ≠ i' → ¬ (M i \ B ⊆ M i' \ B) := by
    intro i i' hne hsub
    apply hincomp i i' hne
    have hBi : B ⊆ M i := (hBMT i).1.le
    have hBi' : B ⊆ M i' := (hBMT i').1.le
    calc M i = M i \ B ∪ B := (Finset.sdiff_union_of_subset hBi).symm
      _ ⊆ M i' \ B ∪ B := Finset.union_subset_union hsub (le_refl B)
      _ = M i' := Finset.sdiff_union_of_subset hBi'
  obtain ⟨i, i', hne, hcomp⟩ :=
    five_diamond_ramsey_property_four_mul_le_five_subsets (T \ B) hcard
      (fun i => M i \ B) hDi_sub
  rcases hcomp with hc | hc
  · exact hDinc i i' hne hc
  · exact hDinc i' i (Ne.symm hne) hc
