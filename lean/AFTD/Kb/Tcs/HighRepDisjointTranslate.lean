import AFTD.Prelude

/-!
# high_rep_disjoint_translate

Topic: combinatorics   Node: 7be532e9b07d

Provenance: helper lemma. arXiv:2610.14496 Proposition 3.1 proof -- When Do Restricted Sumsets Cover a Finite Abelian Group?

Let G be a finite abelian group, A a finite subset of G, and g an element of G. If g does not belong to the 3-fold restricted sumset of A (the set of sums of 3 distinct elements of A), then the set of elements with more than 2 ordered restricted representations as sums of two distinct elements of A is disjoint from g - A.
-/

/-- If an element is missing from the 3-fold restricted sumset, its high-representation set is disjoint from a translate of the subset. -/
theorem high_rep_disjoint_translate {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (g : G)
    (hg : g ∉ (A.powersetCard 3).image (fun s => ∑ x ∈ s, x)) :
    Disjoint
      (Finset.univ.filter (fun x => 2 < ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 = x)).card))
      (A.image (fun a => g - a)) := by
  rw [Finset.disjoint_left]
  intro x hx hx_image
  rw [Finset.mem_filter] at hx
  obtain ⟨-, hx⟩ := hx
  rw [Finset.mem_image] at hx_image
  obtain ⟨a, ha, rfl⟩ := hx_image
  let P := (A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 = g - a)
  have hP_card : 2 < P.card := hx
  have hP_sum : ∀ p ∈ P, p.1 + p.2 = g - a := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.2
  have hex : ∃ p ∈ P, p.1 ≠ a ∧ p.2 ≠ a := by
    by_contra hc
    have h : ∀ p ∈ P, p.1 = a ∨ p.2 = a := by
      intro p hp
      by_cases h1 : p.1 = a
      · exact Or.inl h1
      · refine Or.inr (by_contra fun h2 => hc ⟨p, hp, h1, h2⟩)
    have hsub : P ⊆ {(a, (g - a) - a), ((g - a) - a, a)} := by
      intro p hp
      have hor := h p hp
      have hsum := hP_sum p hp
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hor with h1 | h2
      · left
        ext
        · exact h1
        · rw [← add_sub_cancel_left p.1 p.2, hsum, h1]
      · right
        ext
        · rw [← add_sub_cancel_right p.1 p.2, hsum, h2]
        · exact h2
    have : P.card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  obtain ⟨p, hp, hp1a, hp2a⟩ := hex
  rw [Finset.mem_filter] at hp
  have hpA : p ∈ A ×ˢ A := hp.1
  rw [Finset.mem_product] at hpA
  have huA : p.1 ∈ A := hpA.1
  have hvA : p.2 ∈ A := hpA.2
  have huv : p.1 ≠ p.2 := hp.2.1
  have hsum : p.1 + p.2 = g - a := hp.2.2
  let s : Finset G := {p.1, p.2, a}
  have h1 : p.1 ∉ ({p.2, a} : Finset G) := by
    intro h
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact huv h
    · exact hp1a h
  have h2 : p.2 ∉ ({a} : Finset G) := Finset.notMem_singleton.mpr hp2a
  have hs_card : s.card = 3 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have hs_sub : s ⊆ A := by
    intro y hy
    dsimp [s] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact huA
    · exact hvA
    · exact ha
  have hs_mem : s ∈ A.powersetCard 3 := by
    rw [Finset.mem_powersetCard]
    exact ⟨hs_sub, hs_card⟩
  have hs_sum : ∑ y ∈ s, y = g := by
    dsimp [s]
    rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
    rw [← add_assoc, hsum, sub_add_cancel]
  apply hg
  rw [Finset.mem_image]
  exact ⟨s, hs_mem, hs_sum⟩
