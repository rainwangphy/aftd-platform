import AFTD.Prelude

/-!
# finite_rook_sparse_full_column

Topic: combinatorics   Node: bf6913b8eb36

Provenance: helper lemma. Elementary rook-graph pigeonhole reduction for OP-1027; experiment 27569 checks the four-by-ten case.

Let B be a finite set of cells with m possible rows. Suppose every row is occupied, B has fewer than 2m cells, and every selected cell has at least m−1 other selected cells in its row or column. Then some column contains a selected cell in every row.
-/

theorem finite_rook_sparse_full_column (m : ℕ) {C : Type*} [DecidableEq C] (B : Finset (Fin m × C)) (hrows : ∀ r : Fin m, ∃ c : C, (r,c) ∈ B) (hsize : B.card < 2*m) (hneighbors : ∀ p ∈ B, m-1 ≤ (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card) : ∃ c : C, ∀ r : Fin m, (r,c) ∈ B := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exfalso; omega
  let rowCount : Fin m → ℕ := fun r => (B.filter (fun q => q.1 = r)).card
  have hsum : B.card = ∑ r : Fin m, rowCount r := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun q : Fin m × C => q.1) (t := Finset.univ) (fun q _ => Finset.mem_univ q.1)]
  have hrow_ge : ∀ r : Fin m, 1 ≤ rowCount r := by
    intro r
    obtain ⟨c, hc⟩ := hrows r
    have hmem : (r, c) ∈ B.filter (fun q => q.1 = r) := by simp [Finset.mem_filter, hc]
    have hpos := Finset.card_pos.mpr ⟨(r, c), hmem⟩
    simpa [rowCount] using hpos
  have hsome : ∃ r : Fin m, rowCount r = 1 := by
    by_contra h
    have h2 : ∀ r : Fin m, 2 ≤ rowCount r := by
      intro r
      have h1 := hrow_ge r
      have hne : rowCount r ≠ 1 := fun hh => h ⟨r, hh⟩
      omega
    have hle : ∑ r : Fin m, 2 ≤ ∑ r : Fin m, rowCount r := Finset.sum_le_sum (fun r _ => h2 r)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    rw [← hsum] at hle
    omega
  obtain ⟨r0, hr0⟩ := hsome
  obtain ⟨c0, hc0⟩ := hrows r0
  set p : Fin m × C := (r0, c0) with hp_def
  have hpB : p ∈ B := hc0
  have huniq : ∀ q ∈ B, q.1 = p.1 → q = p := by
    intro q hqB hqrow
    have hq : q ∈ B.filter (fun q => q.1 = r0) := by
      simp only [Finset.mem_filter]
      exact ⟨hqB, hqrow⟩
    have hp : p ∈ B.filter (fun q => q.1 = r0) := by
      simp only [Finset.mem_filter]
      exact ⟨hpB, rfl⟩
    exact Finset.card_le_one.mp (le_of_eq hr0) q hq p hp
  let col := B.filter (fun q => q.2 = p.2)
  have hpcol : p ∈ col := by
    simp [col, Finset.mem_filter, hpB]
  have hN_sub : (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)) ⊆ col.erase p := by
    intro q hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨hqB, hqp, hrowcol⟩ := hq
    rw [Finset.mem_erase]
    refine ⟨hqp, ?_⟩
    simp only [col, Finset.mem_filter]
    exact ⟨hqB, by rcases hrowcol with h | h
                   · exact absurd (huniq q hqB h) hqp
                   · exact h⟩
  have hcol_lower : m ≤ col.card := by
    have hNcard := hneighbors p hpB
    rw [Nat.sub_le_iff_le_add] at hNcard
    have h1 : (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card ≤ (col.erase p).card :=
      Finset.card_le_card hN_sub
    have h2 : (col.erase p).card + 1 = col.card := Finset.card_erase_add_one hpcol
    omega
  have hinj : Set.InjOn (fun q : Fin m × C => q.1) ↑col := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have ha' : a ∈ B ∧ a.2 = p.2 := by simpa only [col, Finset.mem_filter] using ha
    have hb' : b ∈ B ∧ b.2 = p.2 := by simpa only [col, Finset.mem_filter] using hb
    exact Prod.ext hab (ha'.2.trans hb'.2.symm)
  have hcol_upper : col.card ≤ m := by
    have hmaps : Set.MapsTo (fun q : Fin m × C => q.1) ↑col ↑(Finset.univ : Finset (Fin m)) :=
      fun q _ => Finset.mem_univ q.1
    have hle := Finset.card_le_card_of_injOn (fun q : Fin m × C => q.1) hmaps hinj
    rwa [Finset.card_univ, Fintype.card_fin] at hle
  have hcolcard : col.card = m := le_antisymm hcol_upper hcol_lower
  refine ⟨p.2, fun r => ?_⟩
  have himg : col.image (fun q => q.1) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hcolcard, Fintype.card_fin]
  have hr : r ∈ col.image (fun q => q.1) := by rw [himg]; exact Finset.mem_univ r
  obtain ⟨q, hqcol, hqrow⟩ := Finset.mem_image.mp hr
  have hqcol' : q ∈ B ∧ q.2 = p.2 := by
    simpa only [col, Finset.mem_filter] using hqcol
  rw [show (r, p.2) = q from Prod.ext hqrow.symm hqcol'.2.symm]
  exact hqcol'.1
