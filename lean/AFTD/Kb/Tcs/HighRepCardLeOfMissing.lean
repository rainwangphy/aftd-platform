import AFTD.Prelude

/-!
# high_rep_card_le_of_missing

Topic: combinatorics   Node: 9d96925ff10c

Provenance: helper lemma. arXiv:2610.14496 Proposition 3.1 equation (3) -- When Do Restricted Sumsets Cover a Finite Abelian Group?

Let G be a finite abelian group, A a finite subset of G, and g an element of G. If g does not belong to the 3-fold restricted sumset of A (the set of sums of 3 distinct elements of A), then the number of elements with more than 2 ordered restricted representations as sums of two distinct elements of A is at most |G| - |A|.
-/

theorem high_rep_card_le_of_missing_helper {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (g : G)
    (hg : g ∉ (A.powersetCard 3).image (fun s => ∑ x ∈ s, x))
    (a : G) (ha : a ∈ A) :
    ((A ×ˢ A).filter (fun p : G × G => p.1 ≠ p.2 ∧ p.1 + p.2 = g - a)).card ≤ 2 := by
  let S := (A ×ˢ A).filter (fun p : G × G => p.1 ≠ p.2 ∧ p.1 + p.2 = g - a)
  let T : Finset (G × G) := {(a, g - a - a), (g - a - a, a)}
  have hST : S ⊆ T := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    rcases hp with ⟨⟨hp1A, hp2A⟩, hpne, hpsum⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : a = p.1
    · left
      ext
      · exact h1.symm
      · dsimp
        rw [← h1] at hpsum
        exact eq_sub_of_add_eq' hpsum
    · by_cases h2 : a = p.2
      · right
        ext
        · dsimp
          rw [← h2] at hpsum
          exact eq_sub_of_add_eq hpsum
        · exact h2.symm
      · exfalso
        apply hg
        rw [Finset.mem_image]
        refine ⟨{p.1, p.2, a}, ?_, ?_⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp only [Finset.mem_singleton]
              exact Ne.symm h2
            · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hpne, Ne.symm h1⟩
        · have h_not1 : p.1 ∉ ({p.2, a} : Finset G) := by
            simp [hpne, Ne.symm h1]
          have h_not2 : p.2 ∉ ({a} : Finset G) := by
            simp [Ne.symm h2]
          rw [Finset.sum_insert h_not1, Finset.sum_insert h_not2, Finset.sum_singleton,
              ← add_assoc, hpsum, sub_add_cancel]
  exact le_trans (Finset.card_le_card hST) Finset.card_le_two

/-- If an element is missing from the 3-fold restricted sumset, the high-representation set has cardinality at most |G| - |A|. -/
theorem high_rep_card_le_of_missing {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (g : G)
    (hg : g ∉ (A.powersetCard 3).image (fun s => ∑ x ∈ s, x)) :
    (Finset.univ.filter (fun x => 2 < ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 = x)).card)).card ≤
      Fintype.card G - A.card := by
  let X := Finset.univ.filter (fun x => 2 < ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 = x)).card)
  let B := A.image (fun a => g - a)
  have hB_card : B.card = A.card := by
    apply Finset.card_image_of_injective
    intro x y h
    exact sub_right_inj.mp h
  have h_disj : Disjoint X B := by
    rw [Finset.disjoint_right]
    intro x hxB hxX
    rw [Finset.mem_image] at hxB
    rcases hxB with ⟨a, ha, rfl⟩
    rw [Finset.mem_filter] at hxX
    have h_le := high_rep_card_le_of_missing_helper A g hg a ha
    exact not_lt_of_ge h_le hxX.2
  have h_union : X ∪ B ⊆ Finset.univ := Finset.subset_univ _
  have h_card := Finset.card_le_card h_union
  rw [Finset.card_union_of_disjoint h_disj, hB_card, Finset.card_univ] at h_card
  exact Nat.le_sub_of_add_le h_card
