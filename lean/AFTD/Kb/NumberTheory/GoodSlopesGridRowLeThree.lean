import AFTD.Prelude

/-!
# good_slopes_grid_row_le_three

Topic: elementary_number_theory   Node: 0f425c3c843c

Provenance: helper lemma. Counting step in the 105-point good-slope fiber reduction for OP-1027.

If a finite collection has at most seven cells and every nonempty column has at least two cells, every row has at most three cells.
-/

theorem good_slopes_grid_row_le_three {R C : Type*} [DecidableEq R] [DecidableEq C]
    (B : Finset (R × C)) (hcard : B.card ≤ 7)
    (hcols : ∀ c : C, (B.filter fun p => p.2 = c).card = 0 ∨
      2 ≤ (B.filter fun p => p.2 = c).card) (r : R) :
    (B.filter fun p => p.1 = r).card ≤ 3 := by
  classical
  let row := B.filter fun p => p.1 = r
  let cols := row.image Prod.snd
  have hinj : Set.InjOn (fun p : R × C => p.2) row := by
    intro p hp q hq hpq
    apply Prod.ext ?_ hpq
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hcols_card : cols.card = row.card := Finset.card_image_of_injOn hinj
  have hsubset : cols ⊆ B.image Prod.snd :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hlower : ∀ c ∈ cols, 2 ≤ (B.filter fun p => p.2 = c).card := by
    intro c hc
    obtain ⟨p,hp,hpc⟩ := Finset.mem_image.mp hc
    have hpB : p ∈ B := (Finset.mem_filter.mp hp).1
    have hpos : 0 < (B.filter fun p => p.2 = c).card :=
      Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨hpB,hpc⟩⟩
    rcases hcols c with h | h
    · omega
    · exact h
  have htwice : 2 * row.card ≤ B.card := by
    rw [Finset.card_eq_sum_card_image Prod.snd B]
    calc
      2 * row.card = ∑ c ∈ cols, 2 := by simp [hcols_card, Nat.mul_comm]
      _ ≤ ∑ c ∈ cols, (B.filter fun p => p.2 = c).card := Finset.sum_le_sum hlower
      _ ≤ ∑ c ∈ B.image Prod.snd, (B.filter fun p => p.2 = c).card :=
        Finset.sum_le_sum_of_subset hsubset
  change row.card ≤ 3
  omega
