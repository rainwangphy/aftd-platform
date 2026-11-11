import AFTD.Prelude

/-!
# good_slopes_rook_strong_neighbors_rectangle

Topic: elementary_number_theory   Node: 026d223ff180

Provenance: helper lemma. The rook-neighbor reduction for good_slopes_fiber35_colored_gap; compare the finite shape search in experiment 22260.

A nonempty set of at most seven cells in a four-by-six grid is a complete two-by-three rectangle if each selected cell has at least two other selected cells in its row and at least one other selected cell in its column.
-/

open Finset

theorem good_slopes_rook_strong_neighbors_rectangle (B : Finset (Fin 4 × Fin 6)) (hnonempty : B.Nonempty) (hsize : B.card ≤ 7) (hneighbors : ∀ p ∈ B, 2 ≤ (B.filter fun q => q ≠ p ∧ q.1 = p.1).card ∧ 1 ≤ (B.filter fun q => q ≠ p ∧ q.2 = p.2).card) : ∃ (rows : Finset (Fin 4)) (cols : Finset (Fin 6)), rows.card = 2 ∧ cols.card = 3 ∧ B = rows.product cols := by
  classical
  let rows := B.image Prod.fst
  let cols := B.image Prod.snd
  have hrow : ∀ r ∈ rows, 3 ≤ (B.filter fun q => q.1 = r).card := by
    intro r hr
    obtain ⟨p,hp,hpr⟩ := Finset.mem_image.mp hr
    let N := B.filter fun q => q ≠ p ∧ q.1 = p.1
    have hpN : p ∉ N := by simp [N]
    have hsub : insert p N ⊆ B.filter fun q => q.1 = r := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Finset.mem_filter.mpr ⟨hp,hpr⟩
      · have hq' := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hq'.1,hq'.2.2.trans hpr⟩
    have hbound : N.card + 1 ≤ (B.filter fun q => q.1 = r).card := by
      rw [← Finset.card_insert_of_notMem hpN]
      exact Finset.card_le_card hsub
    have hN : 2 ≤ N.card := (hneighbors p hp).1
    omega
  have hcol : ∀ c ∈ cols, 2 ≤ (B.filter fun q => q.2 = c).card := by
    intro c hc
    obtain ⟨p,hp,hpc⟩ := Finset.mem_image.mp hc
    let N := B.filter fun q => q ≠ p ∧ q.2 = p.2
    have hpN : p ∉ N := by simp [N]
    have hsub : insert p N ⊆ B.filter fun q => q.2 = c := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Finset.mem_filter.mpr ⟨hp,hpc⟩
      · have hq' := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hq'.1,hq'.2.2.trans hpc⟩
    have hbound : N.card + 1 ≤ (B.filter fun q => q.2 = c).card := by
      rw [← Finset.card_insert_of_notMem hpN]
      exact Finset.card_le_card hsub
    have hN : 1 ≤ N.card := (hneighbors p hp).2
    omega
  have hsumrow : 3 * rows.card ≤ B.card := by
    rw [Finset.card_eq_sum_card_image Prod.fst B]
    calc
      3 * rows.card = ∑ r ∈ rows, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ r ∈ rows, (B.filter fun q => q.1 = r).card := by
        exact Finset.sum_le_sum fun r hr => hrow r hr
  have hsumcol : 2 * cols.card ≤ B.card := by
    rw [Finset.card_eq_sum_card_image Prod.snd B]
    calc
      2 * cols.card = ∑ c ∈ cols, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ cols, (B.filter fun q => q.2 = c).card := by
        exact Finset.sum_le_sum fun c hc => hcol c hc
  obtain ⟨p,hp⟩ := hnonempty
  have hpr : p.1 ∈ rows := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hpc : p.2 ∈ cols := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  let col := B.filter fun q => q.2 = p.2
  have hinjcol : Set.InjOn (fun q : Fin 4 × Fin 6 => q.1) col := by
    intro x hx y hy heq
    apply Prod.ext heq
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  have hrows : 2 ≤ rows.card := by
    calc
      2 ≤ col.card := hcol p.2 hpc
      _ = (col.image Prod.fst).card := (Finset.card_image_of_injOn hinjcol).symm
      _ ≤ rows.card := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  let row := B.filter fun q => q.1 = p.1
  have hinjrow : Set.InjOn (fun q : Fin 4 × Fin 6 => q.2) row := by
    intro x hx y hy heq
    apply Prod.ext
    · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    · exact heq
  have hcols : 3 ≤ cols.card := by
    calc
      3 ≤ row.card := hrow p.1 hpr
      _ = (row.image Prod.snd).card := (Finset.card_image_of_injOn hinjrow).symm
      _ ≤ cols.card := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  have hr : rows.card = 2 := by omega
  have hc : cols.card = 3 := by omega
  have hsub : B ⊆ rows.product cols := by
    intro q hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,
      Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  have hproduct : (rows.product cols).card = 6 := by simp [hr,hc]
  have hBupper := Finset.card_le_card hsub
  have hB : B.card = 6 := by omega
  exact ⟨rows,cols,hr,hc,Finset.eq_of_subset_of_card_le hsub (by omega)⟩
