import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_neg_two_of_odd_decomp

Topic: elementary_number_theory   Node: be285990215a

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

Every 3-element set of integers with a negative element is {a, a+x, a+y} with a < 0 < x < y.
-/

theorem postage_stamp_number_neg_two_of_odd_decomp
    (A : Finset ℤ) (hA : A.card = 3) (hneg : ∃ a ∈ A, a < 0) :
    ∃ a x y : ℤ, 0 < x ∧ x < y ∧ a < 0 ∧ A = {a, a + x, a + y} := by
  have hne : A.Nonempty := by
    obtain ⟨b, hb, _⟩ := hneg; exact ⟨b, hb⟩
  obtain ⟨b0, hb0, hb0neg⟩ := hneg
  set a := A.min' hne with ha_def
  have ha_mem : a ∈ A := Finset.min'_mem A hne
  have ha_le : ∀ z ∈ A, a ≤ z := fun z hz => Finset.min'_le A z hz
  have ha_neg : a < 0 := lt_of_le_of_lt (ha_le b0 hb0) hb0neg
  set B := A.erase a with hB_def
  have hBcard : B.card = 2 := by
    rw [hB_def, Finset.card_erase_of_mem ha_mem, hA]
  have hBne : B.Nonempty := by rw [← Finset.card_pos]; omega
  set b := B.min' hBne with hb_def
  set c := B.max' hBne with hc_def
  have hb_mem : b ∈ B := Finset.min'_mem B hBne
  have hc_mem : c ∈ B := Finset.max'_mem B hBne
  have hb_memA : b ∈ A := (Finset.mem_erase.mp hb_mem).2
  have hc_memA : c ∈ A := (Finset.mem_erase.mp hc_mem).2
  have hb_ne_a : b ≠ a := (Finset.mem_erase.mp hb_mem).1
  have hb_le_c : b ≤ c := Finset.min'_le B c hc_mem
  have hb_ne_c : b ≠ c := by
    intro hbc
    have hsub : B ⊆ {b} := by
      intro z hz
      simp only [Finset.mem_singleton]
      have h1 : b ≤ z := Finset.min'_le B z hz
      have h2 : z ≤ c := Finset.le_max' B z hz
      omega
    have hc2 := Finset.card_le_card hsub
    rw [hBcard] at hc2
    simp at hc2
  have hbc : b < c := lt_of_le_of_ne hb_le_c hb_ne_c
  have hab : a < b := lt_of_le_of_ne (ha_le b hb_memA) hb_ne_a.symm
  refine ⟨a, b - a, c - a, by omega, by omega, ha_neg, ?_⟩
  have hB_eq : B = {b, c} := by
    have hsub : ({b, c} : Finset ℤ) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hb_mem
      · exact hc_mem
    have hcard : ({b,c} : Finset ℤ).card = 2 := Finset.card_pair hb_ne_c
    have h2 := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hBcard])
    rw [h2]
  have hAeq : A = {a, b, c} := by
    calc A = insert a B := (Finset.insert_erase ha_mem).symm
      _ = insert a {b, c} := by rw [hB_eq]
      _ = {a, b, c} := rfl
  rw [hAeq]
  have e1 : a + (b - a) = b := by ring
  have e2 : a + (c - a) = c := by ring
  rw [e1, e2]
