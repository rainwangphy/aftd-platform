import AFTD.Prelude

/-!
# five_by_five_sparse_defects_have_good_pair

Topic: graphs   Node: c3abfa839b3b

Provenance: helper lemma. OP-1957: finite incidence assembly for the clique-block degree route.

For a relation between two five-element sets, if every row and column has one or two related entries and no related pair has both row and column degree two, there is an unrelated pair whose row and column degrees are both one.
-/

private lemma five_by_five_sparse_defects_have_good_pair_card_prod_filter
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (r : α → β → Prop) [DecidableRel r] :
    ((s ×ˢ t).filter (fun p => r p.1 p.2)).card = ∑ a ∈ s, (t.filter (r a)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.card_filter]

private lemma five_by_five_sparse_defects_have_good_pair_rows_le_cols
    {V : Type*} [DecidableEq V] (A C : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hcol : ∀ c ∈ C, 1 ≤ (A.filter (fun a => R a c)).card ∧
      (A.filter (fun a => R a c)).card ≤ 2)
    (hno22 : ∀ a ∈ A, ∀ c ∈ C, R a c →
      (C.filter (R a)).card = 2 → (A.filter (fun v => R v c)).card ≠ 2) :
    2 * (A.filter (fun a => (C.filter (R a)).card = 2)).card ≤
      (C.filter (fun c => (A.filter (fun v => R v c)).card = 1)).card := by
  classical
  let D2A := A.filter (fun a => (C.filter (R a)).card = 2)
  let D1C := C.filter (fun c => (A.filter (fun v => R v c)).card = 1)
  let P := (D2A ×ˢ C).filter (fun p : V × V => R p.1 p.2)
  have memC : ∀ p ∈ P, p.2 ∈ D1C := by
    intro p hp
    obtain ⟨hpprod, hpR⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpprod
    have hp1A : p.1 ∈ A := Finset.filter_subset _ _ hp1
    have hp1d : (C.filter (R p.1)).card = 2 := (Finset.mem_filter.mp hp1).2
    have hcolp := hcol p.2 hp2
    have hne := hno22 p.1 hp1A p.2 hp2 hpR hp1d
    exact Finset.mem_filter.mpr ⟨hp2, by omega⟩
  have hPcard : P.card = 2 * D2A.card := by
    have hprod : P.card = ∑ a ∈ D2A, (C.filter (R a)).card :=
      five_by_five_sparse_defects_have_good_pair_card_prod_filter D2A C R
    rw [hprod]
    have hconst : ∑ a ∈ D2A, (C.filter (R a)).card = ∑ a ∈ D2A, 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    rw [hconst, Finset.sum_const, Nat.nsmul_eq_mul]
    omega
  have hbound : P.card ≤ D1C.card := by
    apply Finset.card_le_card_of_injOn (fun p : V × V => p.2)
    · intro p hp
      exact memC p hp
    · intro p hp q hq hpq
      have hpc := memC p hp
      have hp1d : (A.filter (fun v => R v p.2)).card = 1 := (Finset.mem_filter.mp hpc).2
      obtain ⟨hpprod, hpR⟩ := Finset.mem_filter.mp hp
      have hpq2 : p.2 = q.2 := hpq
      obtain ⟨hqprod, hqR⟩ := Finset.mem_filter.mp hq
      have hp1A : p.1 ∈ A := Finset.filter_subset _ _ (Finset.mem_product.mp hpprod).1
      have hq1A : q.1 ∈ A := Finset.filter_subset _ _ (Finset.mem_product.mp hqprod).1
      have hmem1 : p.1 ∈ A.filter (fun v => R v p.2) := Finset.mem_filter.mpr ⟨hp1A, hpR⟩
      have hmem2 : q.1 ∈ A.filter (fun v => R v p.2) := by
        rw [← hpq2] at hqR
        exact Finset.mem_filter.mpr ⟨hq1A, hqR⟩
      have heq1 : p.1 = q.1 := Finset.card_le_one.mp (by omega) p.1 hmem1 q.1 hmem2
      exact Prod.ext heq1 hpq2
  calc 2 * (A.filter (fun a => (C.filter (R a)).card = 2)).card
      = 2 * D2A.card := by rfl
    _ = P.card := hPcard.symm
    _ ≤ D1C.card := hbound
    _ = (C.filter (fun c => (A.filter (fun v => R v c)).card = 1)).card := by rfl

theorem five_by_five_sparse_defects_have_good_pair
    {V : Type*} [DecidableEq V] (A C : Finset V) (R : V → V → Prop) [DecidableRel R]
    (hA : A.card=5) (hC : C.card=5)
    (hrow : ∀ a ∈ A, 1 ≤ (C.filter (R a)).card ∧ (C.filter (R a)).card ≤ 2)
    (hcol : ∀ c ∈ C, 1 ≤ (A.filter (fun a => R a c)).card ∧
      (A.filter (fun a => R a c)).card ≤ 2)
    (hno22 : ∀ a ∈ A, ∀ c ∈ C, R a c →
      (C.filter (R a)).card = 2 → (A.filter (fun v => R v c)).card ≠ 2) :
    ∃ a ∈ A, ∃ c ∈ C, ¬ R a c ∧ (C.filter (R a)).card = 1 ∧
      (A.filter (fun v => R v c)).card = 1 := by
  classical
  let D2A := A.filter (fun a => (C.filter (R a)).card = 2)
  let D1A := A.filter (fun a => (C.filter (R a)).card = 1)
  let D2C := C.filter (fun c => (A.filter (fun v => R v c)).card = 2)
  let D1C := C.filter (fun c => (A.filter (fun v => R v c)).card = 1)
  have h1 : 2 * D2A.card ≤ D1C.card :=
    five_by_five_sparse_defects_have_good_pair_rows_le_cols A C R hcol hno22
  have hno' : ∀ c ∈ C, ∀ a ∈ A, R a c → (A.filter (fun v => R v c)).card = 2 →
      (C.filter (fun v => R a v)).card ≠ 2 := by
    intro c hc a ha hR hcd hrd
    exact hno22 a ha c hc hR hrd hcd
  have h2 : 2 * D2C.card ≤ D1A.card :=
    five_by_five_sparse_defects_have_good_pair_rows_le_cols C A (fun c a => R a c) hrow hno'
  have hpartA : D2A.card + D1A.card = A.card := by
    have key := Finset.card_filter_add_card_filter_not (s := A) (p := fun a : V => (C.filter (R a)).card = 2)
    have heq : A.filter (fun a => ¬ (C.filter (R a)).card = 2) = D1A := by
      ext a
      simp only [D1A, Finset.mem_filter]
      constructor
      · rintro ⟨ha, hne⟩
        have := hrow a ha
        exact ⟨ha, by omega⟩
      · rintro ⟨ha, h1⟩
        exact ⟨ha, by omega⟩
    rw [heq] at key
    simpa [D2A] using key
  have hpartC : D2C.card + D1C.card = C.card := by
    have key := Finset.card_filter_add_card_filter_not (s := C) (p := fun c : V => (A.filter (fun a => R a c)).card = 2)
    have heq : C.filter (fun c => ¬ (A.filter (fun a => R a c)).card = 2) = D1C := by
      ext c
      simp only [D1C, Finset.mem_filter]
      constructor
      · rintro ⟨hc, hne⟩
        have := hcol c hc
        exact ⟨hc, by omega⟩
      · rintro ⟨hc, h1⟩
        exact ⟨hc, by omega⟩
    rw [heq] at key
    simpa [D2C] using key
  have hD1Cle : D1C.card ≤ C.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hD1Ale : D1A.card ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
  have ht : D2A.card ≤ 2 := by
    rw [hC] at hD1Cle
    omega
  have hs : D2C.card ≤ 2 := by
    rw [hA] at hD1Ale
    omega
  have hD1A_nonempty : D1A.Nonempty := by
    have hpos : 0 < D1A.card := by
      rw [hA] at hpartA
      omega
    exact Finset.card_pos.mp hpos
  obtain ⟨a, haD1A⟩ := hD1A_nonempty
  have haA : a ∈ A := (Finset.mem_filter.mp haD1A).1
  have hrd_a : (C.filter (R a)).card = 1 := (Finset.mem_filter.mp haD1A).2
  let U := C \ C.filter (R a)
  have hUcard : U.card = 4 := by
    show (C \ C.filter (R a)).card = 4
    have hsub : C.filter (R a) ⊆ C := Finset.filter_subset _ _
    have hcd := Finset.card_sdiff_add_card_eq_card hsub
    rw [hC, hrd_a] at hcd
    omega
  have hnotsub : ¬ U ⊆ D2C := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hUcard] at hle
    omega
  obtain ⟨c, hcU, hcD2C⟩ := Finset.not_subset.mp hnotsub
  obtain ⟨hcC, hcnot⟩ := Finset.mem_sdiff.mp hcU
  have hncR : ¬ R a c := by
    intro hR
    exact hcnot (Finset.mem_filter.mpr ⟨hcC, hR⟩)
  have hcd_c : (A.filter (fun v => R v c)).card = 1 := by
    have hne : (A.filter (fun v => R v c)).card ≠ 2 := by
      intro h2eq
      exact hcD2C (Finset.mem_filter.mpr ⟨hcC, h2eq⟩)
    have := hcol c hcC
    omega
  exact ⟨a, haA, c, hcC, hncR, hrd_a, hcd_c⟩
