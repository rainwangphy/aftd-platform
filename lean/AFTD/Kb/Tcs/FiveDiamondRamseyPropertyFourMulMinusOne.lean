import AFTD.Prelude
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.FiveDiamondLevelColoringIntervalCardLeThree
import AFTD.Kb.Tcs.FiveDiamondLevelColoring
import AFTD.Kb.Tcs.FiveDiamondRamseyPropertyIffSets
import AFTD.Kb.Tcs.PosetRamseyProperty
import AFTD.Kb.Tcs.DiamondPoset

/-!
# five_diamond_ramsey_property_four_mul_minus_one

Topic: combinatorics   Node: 1e9efa283c0d

Provenance: helper lemma. step towards op_270_five_diamond_poset_ramsey_number

For k ≥ 1, the poset Ramsey property for the 5-diamond fails at 4k-1: the level colouring witnesses it, so R_k(D_5) ≥ 4k.
-/

lemma five_diamond_ramsey_property_four_mul_minus_one_antichain_card_le_three
    {α : Type*} [DecidableEq α] {X : Finset α} (hX : X.card ≤ 3)
    (𝒜 : Finset (Finset α)) (hsub : ∀ S ∈ 𝒜, S ⊆ X)
    (hanti : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : 𝒜.card ≤ 3 := by
  classical
  let p : α → Prop := fun a => a ∈ X
  have hinj : Set.InjOn (fun S : Finset α => S.subtype p) (𝒜 : Set (Finset α)) := by
    intro S hS T hT hST
    have hSX : ∀ x ∈ S, p x := fun x hx => hsub S hS hx
    have hTX : ∀ x ∈ T, p x := fun x hx => hsub T hT hx
    have h1 : Finset.map (Function.Embedding.subtype p) (S.subtype p) = S :=
      Finset.subtype_map_of_mem hSX
    have h2 : Finset.map (Function.Embedding.subtype p) (T.subtype p) = T :=
      Finset.subtype_map_of_mem hTX
    have hST' : S.subtype p = T.subtype p := hST
    rw [← h1, ← h2, hST']
  have hcard : (𝒜.image (fun S => S.subtype p)).card = 𝒜.card :=
    Finset.card_image_of_injOn hinj
  have hantiB : IsAntichain (· ⊆ ·) ((𝒜.image (fun S => S.subtype p)) : Set (Finset (Subtype p))) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨S, hS, rfl⟩ := ha
    obtain ⟨T, hT, rfl⟩ := hb
    have hne : S ≠ T := by intro h; exact hab (by rw [h])
    have hsub_of : (S.subtype p) ⊆ (T.subtype p) → S ⊆ T := by
      intro h x hx
      have hxX : p x := hsub S hS hx
      have h1 : (⟨x, hxX⟩ : Subtype p) ∈ S.subtype p := by
        rw [Finset.mem_subtype]; exact hx
      have h2 : (⟨x, hxX⟩ : Subtype p) ∈ T.subtype p := h h1
      rwa [Finset.mem_subtype] at h2
    exact fun hST => hanti hS hT hne (hsub_of hST)
  have hsp := hantiB.sperner
  have hfx : Fintype.card (Subtype p) = X.card := by simp [p]
  rw [hfx] at hsp
  have hle : X.card.choose (X.card / 2) ≤ 3 := by
    interval_cases X.card <;> simp
  omega

lemma five_diamond_ramsey_property_four_mul_minus_one_five_subsets
    {α : Type*} [DecidableEq α] (X : Finset α) (hX : X.card ≤ 3)
    (M : Fin 5 → Finset α) (hM : ∀ i, M i ⊆ X) :
    ∃ i i', i ≠ i' ∧ (M i ⊆ M i' ∨ M i' ⊆ M i) := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective M := by
    intro i j hij
    by_contra hne
    exact (h i j hne).1 (by rw [hij])
  set 𝒜 : Finset (Finset α) := Finset.univ.image M with h𝒜
  have hcard : 𝒜.card = 5 := by
    rw [h𝒜, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : ∀ S ∈ 𝒜, S ⊆ X := by
    intro S hS
    rw [h𝒜, Finset.mem_image] at hS
    obtain ⟨i, -, rfl⟩ := hS
    exact hM i
  have hanti : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, h𝒜, Finset.mem_image] at ha hb
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, rfl⟩ := hb
    have hne : i ≠ j := by intro e; exact hab (by rw [e])
    exact (h i j hne).1
  have := five_diamond_ramsey_property_four_mul_minus_one_antichain_card_le_three hX 𝒜 hsub hanti
  omega

/-- The lower-bound half of R_k(D_5) = 4k: at dimension 4k-1 the level colouring A ↦ min (k-1) (|A|/4) has no monochromatic induced 5-diamond. -/
theorem five_diamond_ramsey_property_four_mul_minus_one (k : ℕ) (hk : 1 ≤ k) :
    ¬ poset_ramsey_property (DiamondPoset 5) k (4 * k - 1) := by
  classical
  intro h
  rw [five_diamond_ramsey_property_iff_sets] at h
  obtain ⟨col, B, T, M, hcB, hcT, hcM, hBT, hBMT, hincomp⟩ :=
    h (five_diamond_level_coloring k (4 * k - 1) hk)
  have hcol_eq :
      five_diamond_level_coloring k (4 * k - 1) hk B =
        five_diamond_level_coloring k (4 * k - 1) hk T := by
    rw [hcB, hcT]
  have hcard : (T \ B).card ≤ 3 :=
    five_diamond_level_coloring_interval_card_le_three k (4 * k - 1) hk (le_refl _) B T hBT hcol_eq
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
    five_diamond_ramsey_property_four_mul_minus_one_five_subsets (T \ B) hcard
      (fun i => M i \ B) hDi_sub
  rcases hcomp with hc | hc
  · exact hDinc i i' hne hc
  · exact hDinc i' i (Ne.symm hne) hc
