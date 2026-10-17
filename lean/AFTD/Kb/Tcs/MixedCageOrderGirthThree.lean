import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphIsValid
import AFTD.Kb.Tcs.MixedGraphIsRegular
import AFTD.Kb.Tcs.MixedGraphHasCycle
import AFTD.Kb.Tcs.MixedGraphHasGirth
import AFTD.Kb.Tcs.MixedCageOrder
import AFTD.Kb.Tcs.MixedGraphCardGeOfIsRegular

/-!
# mixed_cage_order_girth_three

Topic: graphs   Node: 9a4e72bf238f

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Theorem 5.1.

For all r ≥ 1 and z ≥ 1, the minimum order of an (r, z, 3)-mixed cage is n(r, z, 3) = r + 2z + 1.
-/

theorem mixed_cage_order_girth_three (r z : ℕ) (hr : 1 ≤ r) (hz : 1 ≤ z) :
    mixed_cage_order r z 3 = r + 2 * z + 1 := by
  have hNz : NeZero (r + 2 * z + 1) := ⟨by omega⟩
  have H : ∀ (f : Fin (r + 2 * z + 1) ≃ Fin (r + 2 * z + 1)) (a b : ℕ), b < r + 2 * z + 1 →
      {y | a ≤ (f y).val ∧ (f y).val ≤ b}.ncard = b + 1 - a := by
    intro f a b hb
    have e : {y | a ≤ (f y).val ∧ (f y).val ≤ b} = f ⁻¹' {d | a ≤ d.val ∧ d.val ≤ b} := rfl
    rw [e, Set.ncard_preimage_of_injective_subset_range f.injective (by simp),
      ← Set.ncard_image_of_injective _ Fin.val_injective]
    have : Fin.val '' {d : Fin (r + 2 * z + 1) | a ≤ d.val ∧ d.val ≤ b} = ↑(Finset.Icc a b) := by
      ext d
      simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc]
      constructor
      · rintro ⟨e, he, rfl⟩; exact he
      · intro hd; exact ⟨⟨d, by omega⟩, hd, rfl⟩
    rw [this, Set.ncard_coe_finset, Nat.card_Icc]
  have key : ∀ x y : Fin (r + 2 * z + 1), x ≠ y → (y - x).val + (x - y).val = r + 2 * z + 1 := by
    intro x y hxy
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
    · rw [Fin.coe_sub_iff_le.2 (Fin.le_iff_val_le_val.2 h.le),
        Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 h)]; omega
    · rw [Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 h),
        Fin.coe_sub_iff_le.2 (Fin.le_iff_val_le_val.2 h.le)]; omega
  have z0 : ∀ x : Fin (r + 2 * z + 1), (x - x).val = 0 := by simp
  let A : Fin (r + 2 * z + 1) → Fin (r + 2 * z + 1) → Prop :=
    fun x y => 1 ≤ (y - x).val ∧ (y - x).val ≤ z
  let E : SimpleGraph (Fin (r + 2 * z + 1)) :=
    { Adj := fun x y => z + 1 ≤ (y - x).val ∧ (y - x).val ≤ z + r
      symm := ⟨fun (x y : Fin (r + 2 * z + 1))
          (h : z + 1 ≤ (y - x).val ∧ (y - x).val ≤ z + r) => by
        have hxy : x ≠ y := by rintro rfl; rw [z0] at h; omega
        have := key x y hxy
        constructor <;> omega⟩
      loopless := ⟨fun (x : Fin (r + 2 * z + 1))
          (h : z + 1 ≤ (x - x).val ∧ (x - x).val ≤ z + r) => by rw [z0] at h; omega⟩ }
  have hmem : r + 2 * z + 1 ∈ {n | ∃ (E : SimpleGraph (Fin n)) (A : Fin n → Fin n → Prop),
      mixed_graph_is_valid E A ∧ mixed_graph_is_regular E A r z ∧ mixed_graph_has_girth E A 3} := by
    refine ⟨E, A, ⟨fun x h => ?_, fun x y h h' => ?_, fun x y h h' => ?_⟩, fun x => ⟨?_, ?_, ?_⟩,
      ⟨⟨le_rfl, ![⟨0, by omega⟩, ⟨1, by omega⟩, ⟨z + 1, by omega⟩], ?_, ?_⟩,
        fun t ht h => by have := h.1; omega⟩⟩
    · have := h.1; rw [z0] at this; omega
    · have hxy : x ≠ y := by rintro rfl; have := h.1; rw [z0] at this; omega
      have := key x y hxy
      have := h.1; have := h.2; have := h'.1; have := h'.2; omega
    · have := h.1; have := h'.2; omega
    · exact (H (Equiv.subRight x) (z + 1) (z + r) (by omega)).trans (by omega)
    · exact (H (Equiv.subRight x) 1 z (by omega)).trans (by omega)
    · exact (H (Equiv.subLeft x) 1 z (by omega)).trans (by omega)
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff] <;> omega
    · intro i
      fin_cases i
      · right
        show 1 ≤ ((⟨1, _⟩ : Fin (r + 2 * z + 1)) - ⟨0, _⟩).val ∧
          ((⟨1, _⟩ : Fin (r + 2 * z + 1)) - ⟨0, _⟩).val ≤ z
        rw [Fin.coe_sub_iff_le.2 (Fin.le_def.2 (by simp))]; simp only []; omega
      · right
        show 1 ≤ ((⟨z + 1, _⟩ : Fin (r + 2 * z + 1)) - ⟨1, _⟩).val ∧
          ((⟨z + 1, _⟩ : Fin (r + 2 * z + 1)) - ⟨1, _⟩).val ≤ z
        rw [Fin.coe_sub_iff_le.2 (Fin.le_def.2 (by simp))]; simp only []; omega
      · left
        show z + 1 ≤ ((⟨0, _⟩ : Fin (r + 2 * z + 1)) - ⟨z + 1, _⟩).val ∧
          ((⟨0, _⟩ : Fin (r + 2 * z + 1)) - ⟨z + 1, _⟩).val ≤ z + r
        rw [Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 (by simp))]; simp only []; omega
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun n ⟨E, A, hv, hreg, hg⟩ => ?_)
  obtain ⟨-, x, -, -⟩ := hg.1
  have : Nonempty (Fin n) := ⟨x 0⟩
  simpa using mixed_graph_card_ge_of_is_regular E A r z hv hreg
