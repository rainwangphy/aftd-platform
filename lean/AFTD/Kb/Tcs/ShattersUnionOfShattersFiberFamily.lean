import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetFiberFamily
import AFTD.Kb.Tcs.FinsetRestrictedFamily

/-!
# shatters_union_of_shatters_fiber_family

Topic: combinatorics   Node: 670726b2fd29

Provenance: helper lemma. arXiv:2611.06860 Lemma 2.4

Let F be a family of subsets on a finite ground set, S ⊆ J, and let R_{J,S} be the fiber family. If T is shattered by R_{J,S}, then S ∪ T is shattered by F.
-/

/-- If T is shattered by the fiber family R_{J,S}, then S ∪ T is shattered by F. -/
theorem shatters_union_of_shatters_fiber_family {α : Type*} [Fintype α] [DecidableEq α] {ℱ : Finset (Finset α)} {J S T : Finset α} (hS : S ⊆ J) (hT : (finset_fiber_family ℱ J S).Shatters T) : ℱ.Shatters (S ∪ T) := by
  intro Z hZ
  have hT_compl : T ⊆ Jᶜ := by
    intro x hx
    obtain ⟨U, hU, hTU⟩ := hT (Finset.Subset.refl T)
    have hU_sub : U ⊆ Jᶜ := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have : x ∈ T ∩ U := by rw [hTU]; exact hx
    exact hU_sub (Finset.mem_of_mem_inter_right this)
  have hX_sub : Z ∩ T ⊆ T := Finset.inter_subset_right
  obtain ⟨U, hU, hTU⟩ := hT hX_sub
  rw [finset_fiber_family, Finset.mem_filter, Finset.mem_powerset] at hU
  rcases hU with ⟨hU_sub, hU_shatters⟩
  have hY_sub : Z ∩ S ⊆ S := Finset.inter_subset_right
  obtain ⟨A, hA, hSA⟩ := hU_shatters hY_sub
  rw [finset_restricted_family, Finset.mem_filter, Finset.mem_powerset] at hA
  rcases hA with ⟨hA_sub, hAU_in_F⟩
  use A ∪ U, hAU_in_F
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hxST, hxAU⟩
    rcases hxST with hxS | hxT
    · rcases hxAU with hxA | hxU
      · have : x ∈ S ∩ A := Finset.mem_inter.mpr ⟨hxS, hxA⟩
        rw [hSA] at this
        exact (Finset.mem_inter.mp this).1
      · exfalso
        have hxJ := hS hxS
        have hxJc := hU_sub hxU
        rw [Finset.mem_compl] at hxJc
        exact hxJc hxJ
    · rcases hxAU with hxA | hxU
      · exfalso
        have hxJc := hT_compl hxT
        rw [Finset.mem_compl] at hxJc
        have hxJ := hA_sub hxA
        exact hxJc hxJ
      · have : x ∈ T ∩ U := Finset.mem_inter.mpr ⟨hxT, hxU⟩
        rw [hTU] at this
        exact (Finset.mem_inter.mp this).1
  · intro hxZ
    have hxST := Finset.mem_union.mp (hZ hxZ)
    refine ⟨hxST, ?_⟩
    rcases hxST with hxS | hxT
    · left
      have : x ∈ S ∩ A := by
        rw [hSA]
        exact Finset.mem_inter.mpr ⟨hxZ, hxS⟩
      exact (Finset.mem_inter.mp this).2
    · right
      have : x ∈ T ∩ U := by
        rw [hTU]
        exact Finset.mem_inter.mpr ⟨hxZ, hxT⟩
      exact (Finset.mem_inter.mp this).2
