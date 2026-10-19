import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopyColourInjectiveNonempty
import AFTD.Kb.Tcs.HasMonochromaticFanCopyColourInjectiveNonempty
import AFTD.Kb.Tcs.MdfrbfCompressionBound
import AFTD.Kb.Tcs.MdfrbfCompressionCard
import AFTD.Kb.Tcs.MdfrbfFibreSubset
import AFTD.Kb.Tcs.MdfrbfCompress
import AFTD.Kb.Tcs.MdfrbfCompressSubsetIff
import AFTD.Kb.Tcs.MdfrbfDiamondTransfer
import AFTD.Kb.Tcs.MdfrbfFanTransfer
import AFTD.Kb.Tcs.MdfrbfColourInj
import AFTD.Kb.Tcs.MdfrbfFanOfCSubset
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.HasMonochromaticFanCopy

/-!
# mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

Topic: combinatorics   Node: f7d40169a235

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Case b ≥ 2 with every singleton fan-coloured: if d ≥ j*a + (j-1)*b + 1 and the statement holds at (a, b-1) in dimension d-(j-1), then χ has a monochromatic diamond in one of the a diamond colours or a monochromatic F_j in one of the b fan colours.
-/

/-- b ≥ 2 step with all singletons fan-coloured: pigeonhole a colour c on j-1 singletons, compress away that set W, and apply the (a, b-1) instance; a c-coloured set inside the compressed board is already a fan in colour c. -/
theorem mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours (j a b d : ℕ) (hj : 2 ≤ j)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (hd : j * a + (j - 1) * b + 1 ≤ d)
    (ih : mixed_ramsey_property j a (b - 1) (d - (j - 1)))
    (χ : Finset (Fin d) → Fin (a + b))
    (hx : ∀ x : Fin d, ∃ c : Fin b, χ {x} = Fin.natAdd a c) :
    (∃ col : Fin a, has_monochromatic_diamond_copy j d (Fin.castAdd b col) χ) ∨
      ∃ col : Fin b, has_monochromatic_fan_copy j d (Fin.natAdd a col) χ := by
  classical
  let f : Fin d → Fin b := fun x => (hx x).choose
  have hf_spec : ∀ x : Fin d, χ {x} = Fin.natAdd a (f x) := fun x => (hx x).choose_spec
  have hb_gt : b * (j - 2) < d := by
    have hj1 : j - 1 = (j - 2) + 1 := by omega
    have hmul : (j - 1) * b = (j - 2) * b + b := by rw [hj1, Nat.add_mul, one_mul]
    have hja : 1 ≤ j * a := by
      have h : 0 < j * a := Nat.mul_pos (by omega) (by omega)
      omega
    rw [Nat.mul_comm b (j - 2)]
    omega
  obtain ⟨c, W, hWcard, hWf⟩ := mdfrbf_fibre_subset f (j - 2) hb_gt
  have hWcard' : W.card = j - 1 := by omega
  have hWc : ∀ w ∈ W, χ {w} = Fin.natAdd a c := by
    intro w hw; rw [hf_spec w, hWf w hw]
  by_cases hwin : ∃ A : Finset ↥(Finset.univ \ W), A.Nonempty ∧ χ (mdfrbf_compress W χ (Fin.natAdd a c) A) = Fin.natAdd a c
  · right
    set emb : ↥(Finset.univ \ W) ↪ Fin d := Function.Embedding.subtype fun x => x ∈ Finset.univ \ W with hemb
    have hdef : ∀ A : Finset ↥(Finset.univ \ W), mdfrbf_compress W χ (Fin.natAdd a c) A
        = A.map emb ∪ (if (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = Fin.natAdd a c) then W else ∅) := by
      intro A
      unfold mdfrbf_compress
      simp only [← hemb]
      by_cases h : (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = Fin.natAdd a c)
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]; simp
    have hnotW : ∀ x : ↥(Finset.univ \ W), (emb x : Fin d) ∉ W := by
      intro x hx'
      have hx2 : (x : Fin d) ∈ Finset.univ \ W := x.2
      rw [Finset.mem_sdiff] at hx2
      have hv : (emb x : Fin d) = (x : Fin d) := rfl
      rw [hv] at hx'
      exact hx2.2 hx'
    have hdisj : ∀ A : Finset ↥(Finset.univ \ W), Disjoint (A.map emb) W := by
      intro A
      rw [Finset.disjoint_left]
      intro y hy hyW
      rw [Finset.mem_map] at hy
      obtain ⟨x, -, rfl⟩ := hy
      exact hnotW x hyW
    obtain ⟨A, hAne, hAcol⟩ := hwin
    have hH : A.Nonempty ∧ ∃ B, B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = Fin.natAdd a c := by
      by_contra hcon
      have hT : mdfrbf_compress W χ (Fin.natAdd a c) A = A.map emb := by
        rw [hdef A, if_neg hcon]
        simp
      exact hcon ⟨hAne, A, hAne, le_rfl, by rw [← hT]; exact hAcol⟩
    obtain ⟨B, hBne, hBsub, hBcol⟩ := hH.2
    have hT_union : mdfrbf_compress W χ (Fin.natAdd a c) A = A.map emb ∪ W := by
      rw [hdef A, if_pos hH]
    refine ⟨c, mdfrbf_fan_of_c_subset hj W hWcard' χ (Fin.natAdd a c) _ (B.map emb) hAcol ?_ hWc ?_ ?_ hBcol ?_⟩
    · rw [hT_union]; exact Finset.subset_union_right
    · exact hBne.map (f := emb)
    · rw [hT_union]; exact (Finset.map_subset_map.mpr hBsub).trans Finset.subset_union_left
    · exact hdisj B
  · have hnowin : ∀ A : Finset ↥(Finset.univ \ W), A.Nonempty → χ (mdfrbf_compress W χ (Fin.natAdd a c) A) ≠ Fin.natAdd a c := by
      intro A hA hcontra
      exact hwin ⟨A, hA, hcontra⟩
    obtain ⟨f0, hf0_inj, hf0_surj, hf0_cast, hf0_nat, hf0_ne⟩ := mdfrbf_colour_inj a b ha hb c
    let K := d - (j - 1)
    have hKcard : Fintype.card ↥(Finset.univ \ W) = K := mdfrbf_compression_card j d hj W hWcard'
    let e : Fin K ≃ ↥(Finset.univ \ W) :=
      Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact hKcard.symm)
    let T' : Finset (Fin K) → Finset (Fin d) := fun A => mdfrbf_compress W χ (Fin.natAdd a c) (A.map e.toEmbedding)
    have hT' : ∀ A A' : Finset (Fin K), T' A ⊆ T' A' ↔ A ⊆ A' := by
      intro A A'
      simp only [T']
      rw [mdfrbf_compress_subset_iff]
      exact Finset.map_subset_map
    let c₀ : Fin (b - 1) := ⟨0, by omega⟩
    let ψ' : Finset (Fin K) → Fin (a + (b - 1)) := fun B =>
      if h : B.Nonempty then
        Classical.choose (hf0_surj (χ (T' B)) (hnowin (B.map e.toEmbedding) (h.map (f := e.toEmbedding))))
      else Fin.natAdd a c₀
    have hpoint : ∀ B : Finset (Fin K), B.Nonempty → χ (T' B) = f0 (ψ' B) := by
      intro B hB
      have hex : ∃ u : Fin (a + (b - 1)), f0 u = χ (T' B) :=
        hf0_surj (χ (T' B)) (hnowin (B.map e.toEmbedding) (hB.map (f := e.toEmbedding)))
      have hψ : ψ' B = Classical.choose hex := by
        simp only [ψ']
        rw [dif_pos hB]
      rw [hψ]
      exact (Classical.choose_spec hex).symm
    have hempty : ∀ col : Fin a, ψ' ∅ ≠ Fin.castAdd (b - 1) col := by
      intro col
      simp only [ψ']
      rw [dif_neg (Finset.not_nonempty_empty)]
      intro h
      have hv : (Fin.natAdd a c₀).val = (Fin.castAdd (b - 1) col).val := by rw [h]
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      have := col.isLt
      omega
    rcases ih ψ' with ⟨col, hcopy⟩ | ⟨col, hcopy⟩
    · left
      have htr := mdfrbf_diamond_transfer f0 T' hT' χ ψ' hpoint (Fin.castAdd (b - 1) col) (hempty col) hcopy
      rw [hf0_cast col] at htr
      exact ⟨col, htr⟩
    · right
      have htr := mdfrbf_fan_transfer hj f0 T' hT' χ ψ' hpoint (Fin.natAdd a col) hcopy
      obtain ⟨col', hcol'⟩ := hf0_nat col
      rw [hcol'] at htr
      exact ⟨col', htr⟩
