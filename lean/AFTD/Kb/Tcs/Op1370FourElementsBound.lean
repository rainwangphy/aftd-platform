import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370PrivateElementBound

/-!
# op_1370_four_elements_bound

Topic: combinatorics   Node: b8e9e398bc2d

Provenance: original. Related work: arXiv:2611.12199, Conjecture 4.3, specialized to a four-element ground set.

Any at least three nonempty uncomplemented mutually strongly incomparable families on a four-element ground set have total size at most seven.
-/

theorem op_1370_four_elements_bound (t : ℕ) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin 4))) (hne : ∀ i, (𝒜 i).Nonempty) (hunc : ∀ i, is_uncomplemented (𝒜 i)) (hinc : strongly_incomparable 𝒜) : ∑ i, (𝒜 i).card ≤ 7 := by
  classical
  have hother : ∀ i : Fin t, ∃ j : Fin t, j ≠ i := by
    intro i
    have hcard : 1 < (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
    exact ⟨j, (Finset.mem_erase.mp hj).1⟩
  have hempty : ∀ i, (∅ : Finset (Fin 4)) ∉ 𝒜 i := by
    intro i hi
    obtain ⟨j, hji⟩ := hother i
    obtain ⟨B, hB⟩ := hne j
    exact hinc i j (Ne.symm hji) ∅ hi B hB (Finset.empty_subset B)
  have huniv : ∀ i, (Finset.univ : Finset (Fin 4)) ∉ 𝒜 i := by
    intro i hi
    obtain ⟨j, hji⟩ := hother i
    obtain ⟨B, hB⟩ := hne j
    exact hinc j i hji B hB Finset.univ hi (Finset.subset_univ B)
  have hcard3 : ∀ i (S : Finset (Fin 4)) (hS : S ∈ 𝒜 i), S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by
    intro i S hS
    have h0 : S.card ≠ 0 := by
      intro h
      rw [Finset.card_eq_zero] at h
      rw [h] at hS
      exact hempty i hS
    have hle : S.card ≤ 4 := by
      have := Finset.card_le_univ S
      simpa using this
    have h4 : S.card ≠ 4 := by
      intro h
      have hS4 : S.card = Fintype.card (Fin 4) := by simpa using h
      have hSu : S = Finset.univ := Finset.eq_univ_of_card S hS4
      rw [hSu] at hS
      exact huniv i hS
    omega
  by_cases hSingle : ∃ i : Fin t, ∃ S ∈ 𝒜 i, S.card = 1
  · obtain ⟨i, S, hS, hScard1⟩ := hSingle
    obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hScard1
    have hx : ∀ j, j ≠ i → ∀ T ∈ 𝒜 j, x ∉ T := by
      intro j hji T hT hxT
      exact hinc i j (Ne.symm hji) S hS T hT (by rw [hxeq]; exact Finset.singleton_subset_iff.mpr hxT)
    have hb := op_1370_private_element_bound 4 t ht 𝒜 hne hinc i x (hunc i) hx
    norm_num at hb
    exact hb
  · by_cases hThree : ∃ i : Fin t, ∃ S ∈ 𝒜 i, S.card = 3
    · obtain ⟨i0, S0, hS0, hS0card⟩ := hThree
      let ℬ : Fin t → Finset (Finset (Fin 4)) := fun i => (𝒜 i).image compl
      have hBne : ∀ i, (ℬ i).Nonempty := by
        intro i
        obtain ⟨S, hS⟩ := hne i
        exact ⟨Sᶜ, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
      have hBcard : ∀ i, (ℬ i).card = (𝒜 i).card := by
        intro i
        apply Finset.card_image_of_injOn
        intro a _ b _ hab
        have := congrArg compl hab
        simpa using this
      have hBunc : ∀ i, is_uncomplemented (ℬ i) := by
        intro i A hA hAc
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨C, hC, hCeq⟩ := Finset.mem_image.mp hAc
        have hCB : C = Bᶜ := by
          have := congrArg compl hCeq
          simpa using this
        rw [hCB] at hC
        exact hunc i B hB hC
      have hBinc : strongly_incomparable ℬ := by
        intro i j hij A hA B' hB'
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hB'
        intro hsub
        exact hinc j i (Ne.symm hij) T hT S hS (Finset.compl_subset_compl.mp hsub)
      have hScard : S0ᶜ.card = 1 := by
        rw [Finset.card_compl, Fintype.card_fin]
        omega
      obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hScard
      have hmem : ({(x)} : Finset (Fin 4)) ∈ ℬ i0 := by
        exact Finset.mem_image.mpr ⟨S0, hS0, hxeq⟩
      have hx : ∀ j, j ≠ i0 → ∀ T ∈ ℬ j, x ∉ T := by
        intro j hji T hT hxT
        exact hBinc i0 j (Ne.symm hji) {(x)} hmem T hT (Finset.singleton_subset_iff.mpr hxT)
      have hb := op_1370_private_element_bound 4 t ht ℬ hBne hBinc i0 x (hBunc i0) hx
      norm_num at hb
      have hsum : ∑ j, (ℬ j).card = ∑ j, (𝒜 j).card := by
        apply Finset.sum_congr rfl
        intro j _
        exact hBcard j
      rw [hsum] at hb
      exact hb
    · have hall2 : ∀ i (S : Finset (Fin 4)) (hS : S ∈ 𝒜 i), S.card = 2 := by
        intro i S hS
        have h := hcard3 i S hS
        rcases h with h | h | h
        · exact absurd ⟨i, S, hS, h⟩ hSingle
        · exact h
        · exact absurd ⟨i, S, hS, h⟩ hThree
      have hdisj : ∀ i j : Fin t, i ≠ j → Disjoint (𝒜 i) (𝒜 j) := by
        intro i j hij
        rw [Finset.disjoint_left]
        intro S hi hj
        exact hinc i j hij S hi S hj (Finset.Subset.refl S)
      have hsumEq : (Finset.univ.biUnion 𝒜).card = ∑ i, (𝒜 i).card := by
        rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
      have hsub : Finset.univ.biUnion 𝒜 ⊆ Finset.univ.powersetCard 2 := by
        intro S hS
        rw [Finset.mem_powersetCard]
        obtain ⟨i, _, hiS⟩ := Finset.mem_biUnion.mp hS
        exact ⟨Finset.subset_univ S, hall2 i S hiS⟩
      have hcard6 : (Finset.univ.powersetCard 2 : Finset (Finset (Fin 4))).card = 6 := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        decide
      have hle := Finset.card_le_card hsub
      rw [hcard6] at hle
      rw [hsumEq] at hle
      omega
