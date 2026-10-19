import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy

/-!
# mdfrbf_fan_of_c_subset

Topic: combinatorics   Node: 641d92eb32e2

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

Fan witness from a c-coloured block: if W has j-1 points, each of whose singletons is c-coloured, and B is a nonempty c-coloured subset of a c-coloured set top which contains W and is disjoint from B, then there is a monochromatic F_j in colour c (top, with the j-1 singletons of W plus B as middles).
-/

/-- Builds the monochromatic fan in colour c out of the j-1 c-coloured singletons of W together with one c-coloured nonempty set B inside the c-coloured top. -/
theorem mdfrbf_fan_of_c_subset {j d k : ℕ} (hj : 2 ≤ j) (W : Finset (Fin d)) (hW : W.card = j - 1)
    (χ : Finset (Fin d) → Fin k) (c : Fin k) (top B : Finset (Fin d))
    (hcol : χ top = c) (hWtop : W ⊆ top) (hWc : ∀ w ∈ W, χ {w} = c)
    (hBne : B.Nonempty) (hBsub : B ⊆ top) (hBcol : χ B = c) (hBdisj : Disjoint B W) :
    has_monochromatic_fan_copy j d c χ := by
  classical
  let S : Finset (Finset (Fin d)) := insert B (W.image (fun w => ({w} : Finset (Fin d))))
  have hSdef : S = insert B (W.image (fun w => ({w} : Finset (Fin d)))) := rfl
  have hBnotmem : B ∉ W.image (fun w => ({w} : Finset (Fin d))) := by
    intro h
    obtain ⟨w, hw, hwB⟩ := Finset.mem_image.mp h
    obtain ⟨b, hbB⟩ := hBne
    have hbw : b = w := by
      rw [← hwB] at hbB
      exact Finset.mem_singleton.mp hbB
    have hbB' : b ∈ B := by
      rw [← hwB]
      exact Finset.mem_singleton.mpr hbw
    exact (Finset.disjoint_left.mp hBdisj hbB') (hbw ▸ hw)
  have hSimgcard : (W.image (fun w => ({w} : Finset (Fin d)))).card = W.card :=
    Finset.card_image_of_injective W (fun a b h => Finset.singleton_inj.mp h)
  have hScard : S.card = j := by
    rw [hSdef, Finset.card_insert_of_notMem hBnotmem, hSimgcard, hW]
    omega
  let e : ↥S ≃ Fin j := (Finset.equivFin S).trans (finCongr hScard)
  have hWne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.card_empty] at hW
    omega
  have hSprop : ∀ X ∈ S, X ⊆ top ∧ χ X = c ∧ X ≠ top := by
    intro X hX
    rw [hSdef, Finset.mem_insert] at hX
    rcases hX with hXB | hX
    · rw [hXB]
      refine ⟨hBsub, hBcol, ?_⟩
      intro hEq
      obtain ⟨w, hw⟩ := hWne
      have hwt : w ∈ top := hWtop hw
      rw [← hEq] at hwt
      exact (Finset.disjoint_left.mp hBdisj hwt) hw
    · obtain ⟨w, hw, hwX⟩ := Finset.mem_image.mp hX
      rw [← hwX]
      refine ⟨Finset.singleton_subset_iff.mpr (hWtop hw), hWc w hw, ?_⟩
      intro hEq
      obtain ⟨b, hbB⟩ := hBne
      have hbt : b ∈ top := hBsub hbB
      rw [← hEq] at hbt
      have hbw : b = w := Finset.mem_singleton.mp hbt
      have hbW : b ∈ W := hbw ▸ hw
      exact (Finset.disjoint_left.mp hBdisj hbB) hbW
  have hanti : ∀ X ∈ S, ∀ Y ∈ S, X ⊆ Y → X = Y := by
    intro X hX Y hY hsub
    rw [hSdef, Finset.mem_insert] at hX hY
    rcases hX with hXB | hX
    · rw [hXB] at hsub ⊢
      rcases hY with hYB | hY
      · rw [hYB]
      · obtain ⟨w, hw, hwY⟩ := Finset.mem_image.mp hY
        rw [← hwY] at hsub ⊢
        exfalso
        obtain ⟨b, hbB⟩ := hBne
        have hbw : b = w := Finset.mem_singleton.mp (hsub hbB)
        exact (Finset.disjoint_left.mp hBdisj hbB) (hbw ▸ hw)
    · obtain ⟨w, hw, hwX⟩ := Finset.mem_image.mp hX
      rw [← hwX] at hsub ⊢
      rcases hY with hYB | hY
      · rw [hYB] at hsub ⊢
        exfalso
        have hwB : w ∈ B := hsub (Finset.mem_singleton.mpr rfl)
        exact (Finset.disjoint_left.mp hBdisj hwB) hw
      · obtain ⟨w', hw', hwY⟩ := Finset.mem_image.mp hY
        rw [← hwY] at hsub ⊢
        have hww' : w = w' := Finset.mem_singleton.mp (hsub (Finset.mem_singleton.mpr rfl))
        rw [hww']
  refine ⟨top, hcol, fun i => ((e.symm i : ↥S) : Finset (Fin d)), ?_, ?_⟩
  · intro i
    have hmem : ((e.symm i : ↥S) : Finset (Fin d)) ∈ S := (e.symm i).2
    obtain ⟨hsub, hcolmid, hne⟩ := hSprop _ hmem
    exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩, hcolmid⟩
  · intro i i' hne hsub
    exact hne (e.symm.injective (Subtype.ext (hanti _ (e.symm i).2 _ (e.symm i').2 hsub)))
