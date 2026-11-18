import AFTD.Prelude

/-!
# good_slopes_five_levels_no_vertical

Topic: elementary_number_theory   Node: d7a2ed89b0a0

Provenance: helper lemma. The vertical-slice counting step for the 55-point fiber in OP-1027.

A finite set has five rows and five columns, each of size eleven. If each x-fiber has at most fifteen points, each row-column-x fiber at most three, and x is either constant or injective on each column, then x cannot be constant on a row.
-/

theorem good_slopes_five_levels_no_vertical
    {α : Type} [DecidableEq α] (S : Finset α) (row col : α → Fin 5) (x : α → Fin 11)
    (hrows : ∀ i, (S.filter fun p => row p = i).card = 11)
    (hcols : ∀ j, (S.filter fun p => col p = j).card = 11)
    (hbound : ∀ k, (S.filter fun p => x p = k).card ≤ 15)
    (hcross : ∀ i j k, (S.filter fun p => row p = i ∧ col p = j ∧ x p = k).card ≤ 3)
    (hclass : ∀ j, (∃ k, ∀ p ∈ S, col p = j → x p = k) ∨
      Set.InjOn x {p | p ∈ S ∧ col p = j}) :
    ∀ i k, ¬ ∀ p ∈ S, row p = i → x p = k := by
  classical
  intro i k hconst
  set bad : Fin 5 → Prop := fun j => ∀ p ∈ S, col p = j → x p = k with hbaddef
  set Tj : Fin 5 → Finset α := fun j => S.filter (fun p => row p = i ∧ col p = j) with hTjdef
  have hbad_le_one : (Finset.univ.filter bad).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    have hdisj : Disjoint (S.filter fun p => col p = a) (S.filter fun p => col p = b) := by
      rw [Finset.disjoint_filter]
      intro p hp hpa hpb
      exact hab (hpa.symm.trans hpb)
    have hsub : (S.filter fun p => col p = a) ∪ (S.filter fun p => col p = b) ⊆
        S.filter (fun p => x p = k) := by
      intro p hp
      simp only [Finset.mem_union, Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpS, hpa⟩ | ⟨hpS, hpb⟩
      · exact ⟨hpS, ha p hpS hpa⟩
      · exact ⟨hpS, hb p hpS hpb⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hcols a, hcols b] at hcard
    have hb15 := hbound k
    omega
  have hb : ∀ j, (Tj j).card ≤ (if bad j then 3 else 1) := by
    intro j
    by_cases hbj : bad j
    · rw [if_pos hbj]
      have hsub : Tj j ⊆ S.filter (fun p => row p = i ∧ col p = j ∧ x p = k) := by
        intro p hp
        simp only [hTjdef, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, hp.2.2, hconst p hp.1 hp.2.1⟩
      exact le_trans (Finset.card_le_card hsub) (hcross i j k)
    · rw [if_neg hbj]
      rcases hclass j with ⟨k', hk'⟩ | hinj
      · have hle1 : (Tj j).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb2
          simp only [hTjdef, Finset.mem_filter] at ha
          have h1 : x a = k' := hk' a ha.1 ha.2.2
          have h2 : x a = k := hconst a ha.1 ha.2.1
          exact absurd (fun q hqS hqcol => (hk' q hqS hqcol).trans (h1.symm.trans h2)) hbj
        exact hle1
      · have hle1 : (Tj j).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb2
          simp only [hTjdef, Finset.mem_filter] at ha hb2
          have hxa : x a = k := hconst a ha.1 ha.2.1
          have hxb : x b = k := hconst b hb2.1 hb2.2.1
          have hxx : x a = x b := by rw [hxa, hxb]
          exact hinj ⟨ha.1, ha.2.2⟩ ⟨hb2.1, hb2.2.2⟩ hxx
        exact hle1
  have hsum_eq_11 : ∑ j : Fin 5, (Tj j).card = 11 := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (f := col) (s := S.filter (fun p => row p = i)) (t := Finset.univ)
      (fun p _ => by simp)
    rw [hrows i] at hfiber
    rw [hfiber]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hTjdef, Finset.filter_filter]
  have hbound7 : ∑ j : Fin 5, (if bad j then 3 else 1) ≤ 7 := by
    have heq : ∑ j : Fin 5, (if bad j then 3 else 1) = 5 + 2 * (Finset.univ.filter bad).card := by
      have hpt : ∀ j : Fin 5, (if bad j then 3 else 1) = 1 + 2 * (if bad j then (1:ℕ) else 0) := by
        intro j; split <;> rfl
      have h1 : (∑ j : Fin 5, (1:ℕ)) = 5 := by simp
      calc ∑ j : Fin 5, (if bad j then 3 else 1)
          = ∑ j : Fin 5, (1 + 2 * (if bad j then (1:ℕ) else 0)) := by
              apply Finset.sum_congr rfl; intro j _; exact hpt j
        _ = ∑ j : Fin 5, (1:ℕ) + ∑ j : Fin 5, 2 * (if bad j then (1:ℕ) else 0) := by
              rw [Finset.sum_add_distrib]
        _ = 5 + 2 * ∑ j : Fin 5, (if bad j then (1:ℕ) else 0) := by
              rw [← Finset.mul_sum, h1]
        _ = 5 + 2 * (Finset.univ.filter bad).card := by
              rw [Finset.card_filter]
    rw [heq]
    omega
  have hsum_le : ∑ j : Fin 5, (Tj j).card ≤ ∑ j : Fin 5, (if bad j then 3 else 1) :=
    Finset.sum_le_sum (fun j _ => hb j)
  have : 11 ≤ 7 := by rw [← hsum_eq_11]; exact le_trans hsum_le hbound7
  omega
