import AFTD.Prelude

/-!
# cross_pair_orientation_capacity

Topic: graphs   Node: 38ac78cb3934

Provenance: helper lemma. Cross-arc counting reduction in the general minimum-counterexample route to OP-110; experiments 12590 and 12591.

A two-row grid with 2s−1 columns cannot orient all its entries so that each row has at most one entry of the first orientation and all but at most s−1 columns have at most one entry of the second orientation, for s at least three.
-/

theorem cross_pair_orientation_capacity (s : ℕ) (hs : 3 ≤ s) (P : Fin 2 → Fin (2 * s - 1) → Bool) (T : Finset (Fin (2 * s - 1))) (hT : T.card ≤ s - 1) (hrow : ∀ i, (Finset.univ.filter fun j => P i j = true).card ≤ 1) (hcol : ∀ j, j ∉ T → (Finset.univ.filter fun i => P i j = false).card ≤ 1) : False := by
  classical
  let total : ℕ := (Finset.univ.filter (fun p : Fin 2 × Fin (2 * s - 1) => P p.1 p.2 = true)).card
  have htotal_row : total = ∑ i : Fin 2, (Finset.univ.filter (fun j => P i j = true)).card := by
    dsimp [total]
    rw [show (Finset.univ : Finset (Fin 2 × Fin (2 * s - 1))) =
        (Finset.univ : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin (2 * s - 1))) by simp]
    rw [Finset.card_filter]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.card_filter]
  have htotal_col : total =
      ∑ j : Fin (2 * s - 1), (Finset.univ.filter (fun i : Fin 2 => P i j = true)).card := by
    dsimp [total]
    rw [show (Finset.univ : Finset (Fin 2 × Fin (2 * s - 1))) =
        (Finset.univ : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin (2 * s - 1))) by simp]
    rw [Finset.card_filter]
    rw [Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.card_filter]
  have htotal_le : total ≤ 2 := by
    rw [htotal_row]
    calc
      (∑ i : Fin 2, (Finset.univ.filter fun j => P i j = true).card) ≤ ∑ i : Fin 2, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hrow i
      _ = 2 := by simp
  have hout_card : s ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff]
    simp
    omega
  have htrue_ge_one : ∀ j, j ∉ T → 1 ≤ (Finset.univ.filter fun i : Fin 2 => P i j = true).card := by
    intro j hj
    have hfalse := hcol j hj
    have hpart : (Finset.univ.filter (fun i : Fin 2 => P i j = true)).card +
        (Finset.univ.filter (fun i : Fin 2 => P i j = false)).card = 2 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 2)))
        (p := fun i => P i j = true)
      simpa [Fintype.card_fin] using h
    omega
  have hsum_out_ge : (Finset.univ \ T).card ≤
      ∑ j ∈ (Finset.univ \ T), (Finset.univ.filter fun i : Fin 2 => P i j = true).card := by
    simpa using Finset.card_nsmul_le_sum (s := (Finset.univ \ T))
      (f := fun j => (Finset.univ.filter fun i : Fin 2 => P i j = true).card) (n := 1)
      (by
        intro j hj
        exact htrue_ge_one j (by simpa using hj))
  have hsum_le_col : (∑ j ∈ (Finset.univ \ T), (Finset.univ.filter fun i : Fin 2 => P i j = true).card) ≤
      ∑ j : Fin (2 * s - 1), (Finset.univ.filter fun i : Fin 2 => P i j = true).card := by
    exact Finset.sum_le_sum_of_subset (by simp)
  have htotal_ge : s ≤ total := by
    rw [htotal_col]
    exact le_trans hout_card (le_trans hsum_out_ge hsum_le_col)
  omega
