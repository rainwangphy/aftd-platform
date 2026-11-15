import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteRookSparseFullColumn

/-!
# finite_rook_four_sparse_pattern

Topic: combinatorics   Node: 1540060cadf0

Provenance: helper lemma. Rook-graph reduction for the 55-point colored fiber case of OP-1027, supported by experiment 27569.

Let B be a set of at most seven cells in four rows, with every row occupied. If every cell of B has at least three other cells of B in its row or column, then some column contains all four rows; outside that column there are either no cells, or exactly three cells sharing a row or sharing a column.
-/

private lemma finite_rook_four_sparse_pattern_three_cells {C : Type*} [DecidableEq C] {p q r : Fin 4 × C}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : p.1 = q.1 ∨ p.2 = q.2) (h2 : p.1 = r.1 ∨ p.2 = r.2) (h3 : q.1 = r.1 ∨ q.2 = r.2) :
    (∃ a, p.1 = a ∧ q.1 = a ∧ r.1 = a) ∨ (∃ b, p.2 = b ∧ q.2 = b ∧ r.2 = b) := by
  by_cases hp : p.1 = q.1
  · by_cases hpr1 : p.1 = r.1
    · left; exact ⟨p.1, rfl, hp.symm, hpr1.symm⟩
    · have h2' : p.2 = r.2 := by rcases h2 with h | h; exact absurd h hpr1; exact h
      rcases h3 with h3 | h3
      · exact absurd (hp.trans h3) hpr1
      · right; exact ⟨p.2, rfl, h3.trans h2'.symm, h2'.symm⟩
  · have h1' : p.2 = q.2 := by rcases h1 with h | h; exact absurd h hp; exact h
    by_cases hpr2 : p.2 = r.2
    · right; exact ⟨p.2, rfl, h1'.symm, hpr2.symm⟩
    · have h2' : p.1 = r.1 := by rcases h2 with h | h; exact h; exact absurd h hpr2
      rcases h3 with h3 | h3
      · exact absurd (h2'.trans h3.symm) hp
      · exact absurd (h1'.trans h3) hpr2

theorem finite_rook_four_sparse_pattern {C : Type*} [DecidableEq C] (B : Finset (Fin 4 × C)) (hrows : ∀ r : Fin 4, ∃ c : C, (r,c) ∈ B) (hsize : B.card ≤ 7) (hneighbors : ∀ p ∈ B, 3 ≤ (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card) : ∃ c : C, (∀ r : Fin 4, (r,c) ∈ B) ∧ (let E := B.filter fun p => p.2 ≠ c; E.card = 0 ∨ (E.card = 3 ∧ ((∃ r : Fin 4, ∀ p ∈ E, p.1 = r) ∨ (∃ d : C, ∀ p ∈ E, p.2 = d)))) := by
  obtain ⟨c, hc⟩ := finite_rook_sparse_full_column 4 B hrows (by omega) hneighbors
  refine ⟨c, hc, ?_⟩
  dsimp only
  set E := B.filter (fun p => p.2 ≠ c) with hE
  set S : Finset (Fin 4 × C) := Finset.univ.image (fun r : Fin 4 => (r, c)) with hS
  have hScard : S.card = 4 := by
    rw [hS, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h), Finset.card_univ]
    simp
  have hSsub : S ⊆ B := by
    intro x hx
    rw [hS] at hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨r, rfl⟩ := hx
    exact hc r
  have hEsub : E ⊆ B \ S := by
    intro p hp
    rw [hE] at hp
    simp only [Finset.mem_filter] at hp
    refine Finset.mem_sdiff.mpr ⟨hp.1, ?_⟩
    intro hpS
    rw [hS] at hpS
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hpS
    obtain ⟨r, hr⟩ := hpS
    have : p.2 = c := by rw [← hr]
    exact hp.2 this
  have hEcard : E.card ≤ 3 := by
    have h1 : E.card ≤ (B \ S).card := Finset.card_le_card hEsub
    rw [Finset.card_sdiff] at h1
    have hinter : S ∩ B = S := Finset.inter_eq_left.mpr hSsub
    rw [hinter, hScard] at h1
    omega
  have hsub : ∀ p ∈ E, (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)) ⊆
      insert (p.1, c) (E.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)) := by
    intro p hpE q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqB, hqne, hqrc⟩ := hq
    obtain ⟨hpB, hpc⟩ := Finset.mem_filter.mp (hE ▸ hpE)
    by_cases hqc : q.2 = c
    · have hqeq : q = (p.1, c) := by
        refine Prod.ext ?_ hqc
        rcases hqrc with h | h
        · exact h
        · exact absurd (h.symm.trans hqc) hpc
      rw [Finset.mem_insert]
      exact Or.inl hqeq
    · rw [Finset.mem_insert]
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hqB, hqc⟩, hqne, hqrc⟩)
  have hN : ∀ p ∈ E, 2 ≤ (E.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card := by
    intro p hpE
    obtain ⟨hpB, hpc⟩ := Finset.mem_filter.mp (hE ▸ hpE)
    have h1 : 3 ≤ (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card := hneighbors p hpB
    have h2 : (B.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card ≤
        (insert (p.1, c) (E.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2))).card :=
      Finset.card_le_card (hsub p hpE)
    have h3 := Finset.card_insert_le (p.1, c) (E.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2))
    omega
  have hsub2 : ∀ a, (E.filter fun q => q ≠ a ∧ (q.1 = a.1 ∨ q.2 = a.2)) ⊆ E.erase a := by
    intro a q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_erase]
    exact ⟨hq.2.1, hq.1⟩
  rcases Nat.eq_zero_or_pos E.card with h0 | hpos
  · exact Or.inl h0
  · obtain ⟨p, hpE⟩ := Finset.card_pos.mp hpos
    have hNp : 2 ≤ (E.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card := hN p hpE
    have hle : (E.filter fun q => q ≠ p ∧ (q.1 = p.1 ∨ q.2 = p.2)).card ≤ (E.erase p).card :=
      Finset.card_le_card (hsub2 p)
    have herase : (E.erase p).card = E.card - 1 := Finset.card_erase_of_mem hpE
    have hE3 : E.card = 3 := by omega
    refine Or.inr ⟨hE3, ?_⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, hExyz⟩ := Finset.card_eq_three.mp hE3
    have hxE : x ∈ E := by rw [hExyz]; simp
    have hyE : y ∈ E := by rw [hExyz]; simp
    have hzE : z ∈ E := by rw [hExyz]; simp
    have hpair : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → (a.1 = b.1 ∨ a.2 = b.2) := by
      intro a haE b hbE hab
      have hNa : 2 ≤ (E.filter fun q => q ≠ a ∧ (q.1 = a.1 ∨ q.2 = a.2)).card := hN a haE
      have heq : (E.filter fun q => q ≠ a ∧ (q.1 = a.1 ∨ q.2 = a.2)) = E.erase a := by
        apply Finset.eq_of_subset_of_card_le (hsub2 a)
        rw [Finset.card_erase_of_mem haE]
        omega
      have hb : b ∈ E.filter fun q => q ≠ a ∧ (q.1 = a.1 ∨ q.2 = a.2) := by
        rw [heq]
        exact Finset.mem_erase.mpr ⟨Ne.symm hab, hbE⟩
      rcases (Finset.mem_filter.mp hb).2.2 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hcomb := finite_rook_four_sparse_pattern_three_cells hxy hxz hyz
      (hpair x hxE y hyE hxy) (hpair x hxE z hzE hxz) (hpair y hyE z hzE hyz)
    rcases hcomb with ⟨a, hxa, hya, hza⟩ | ⟨b, hxb, hyb, hzb⟩
    · left
      refine ⟨a, ?_⟩
      intro q hqE
      rw [hExyz] at hqE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqE
      rcases hqE with rfl | rfl | rfl
      · exact hxa
      · exact hya
      · exact hza
    · right
      refine ⟨b, ?_⟩
      intro q hqE
      rw [hExyz] at hqE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqE
      rcases hqE with rfl | rfl | rfl
      · exact hxb
      · exact hyb
      · exact hzb
