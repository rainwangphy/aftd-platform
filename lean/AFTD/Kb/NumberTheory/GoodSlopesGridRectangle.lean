import AFTD.Prelude

/-!
# good_slopes_grid_rectangle

Topic: elementary_number_theory   Node: 8927f3cfc3df

Provenance: helper lemma. Counting step in the 105-point good-slope fiber reduction for OP-1027.

If a nonempty finite collection of cells has at most seven cells, each row has either zero or three cells, and every nonempty column has at least two cells, then it is the Cartesian product of two rows and three columns.
-/

theorem good_slopes_grid_rectangle {R C : Type*} [DecidableEq R] [DecidableEq C]
    (B : Finset (R × C)) (hne : B.Nonempty) (hcard : B.card ≤ 7)
    (hrows : ∀ r : R, (B.filter fun p => p.1 = r).card = 0 ∨
      (B.filter fun p => p.1 = r).card = 3)
    (hcols : ∀ c : C, (B.filter fun p => p.2 = c).card = 0 ∨
      2 ≤ (B.filter fun p => p.2 = c).card) :
    ∃ A : Finset R, ∃ T : Finset C, A.card = 2 ∧ T.card = 3 ∧ B = A ×ˢ T := by
  classical
  let A := B.image Prod.fst
  let T := B.image Prod.snd
  have hsumrow : B.card = A.card * 3 := by
    rw [Finset.card_eq_sum_card_image Prod.fst B]
    apply Finset.sum_const_nat
    intro r hr
    have hrpos : 0 < (B.filter fun p => p.1 = r).card := by
      obtain ⟨p,hp,hpr⟩ := Finset.mem_image.mp hr
      exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp,hpr⟩⟩
    rcases hrows r with h | h
    · omega
    · exact h
  obtain ⟨p,hp⟩ := hne
  let col := B.filter fun q => q.2 = p.2
  have hpcol : p ∈ col := Finset.mem_filter.mpr ⟨hp,rfl⟩
  have hcol : 2 ≤ col.card := by
    rcases hcols p.2 with h | h
    · have : 0 < col.card := Finset.card_pos.mpr ⟨p,hpcol⟩
      dsimp [col] at *
      omega
    · exact h
  have hinj : Set.InjOn (fun p : R × C => p.1) col := by
    intro x hx y hy hxy
    apply Prod.ext hxy
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  have hAsmall : 2 ≤ A.card := by
    calc
      2 ≤ col.card := hcol
      _ = (col.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ A.card := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  have hA : A.card = 2 := by omega
  have hcol_exact : ∀ c ∈ T, (B.filter fun p => p.2 = c).card = 2 := by
    intro c hc
    let D := B.filter fun p => p.2 = c
    obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp hc
    have hpos : 0 < D.card := Finset.card_pos.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hqc⟩⟩
    have hlow : 2 ≤ D.card := by
      rcases hcols c with h | h
      · dsimp [D] at *; omega
      · exact h
    have hinj' : Set.InjOn (fun p : R × C => p.1) D := by
      intro x hx y hy hxy
      apply Prod.ext hxy
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hupp : D.card ≤ 2 := by
      calc
        D.card = (D.image Prod.fst).card := (Finset.card_image_of_injOn hinj').symm
        _ ≤ A.card := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
        _ = 2 := hA
    change D.card = 2
    omega
  have hsumcol : B.card = T.card * 2 := by
    rw [Finset.card_eq_sum_card_image Prod.snd B]
    exact Finset.sum_const_nat hcol_exact
  have hT : T.card = 3 := by omega
  refine ⟨A,T,hA,hT,?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩
  · rw [Finset.card_product,hA,hT]
    omega
