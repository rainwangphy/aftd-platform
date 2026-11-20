import AFTD.Prelude

/-!
# graph_two_mixed_bridge_complements_degree_obstruction

Topic: graphs   Node: ca05fcb3d602

Provenance: helper lemma. OP-1957: mixed-size complement bridge degree obstruction for odd parameters; experiments 34687 and 34688.

For j at least nine, the displayed balanced or unbalanced complement bridge block cannot coexist with a second allowed bridge block when the new endpoint has at most one complement neighbor in the first nonendpoint side and the maximum degree is at most j+2.
-/

theorem graph_two_mixed_bridge_complements_degree_obstruction
    (n j : ℕ) (hj : 9 ≤ j) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hmax : ∀ x, H.degree x ≤ j+2)
    (A B A' B' : Finset (Fin n))
    (hAB : Disjoint A B) (hAB' : Disjoint A' B')
    (hold : (A.card = j-2 ∧ B.card = j+2) ∨ (A.card = j ∧ B.card = j))
    (hnew : (A'.card = j-2 ∧ B'.card = j+2) ∨ (A'.card = j ∧ B'.card = j) ∨ (A'.card = j+2 ∧ B'.card = j-2))
    (u v a w : Fin n) (hu : u ∈ A) (hv : v ∈ B) (huv : ¬ H.Adj u v)
    (ha : a ∈ A) (hau : a ≠ u) (hwA : w ∉ A) (hwB : w ∉ B) (ha' : a ∈ A') (hw' : w ∈ B')
    (hcross : ∀ x ∈ A, ∀ y ∈ B, (x = u ∧ y = v) ∨ H.Adj x y)
    (hcross' : ∀ x ∈ A', ∀ y ∈ B', (x = a ∧ y = w) ∨ H.Adj x y)
    (haw : ¬ H.Adj a w) (havoid : ((A.erase u).filter (fun x => H.Adj w x)).card ≤ 1) : False := by
  classical
  have hNa : B ∪ B'.erase w ⊆ H.neighborFinset a := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hy with hyB | hyB'
    · rcases hcross a ha y hyB with ⟨h, -⟩ | h
      · exact absurd h hau
      · exact h
    · obtain ⟨hyw, hyB'⟩ := Finset.mem_erase.mp hyB'
      rcases hcross' a ha' y hyB' with ⟨-, h⟩ | h
      · exact absurd h hyw
      · exact h
  have hcardNa := Finset.card_le_card hNa
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcardNa
  have hdega := hmax a
  have hEr : (B'.erase w).card = B'.card - 1 := Finset.card_erase_of_mem hw'
  have hB'pos : 0 < B'.card := Finset.card_pos.mpr ⟨w, hw'⟩
  have hui := Finset.card_union_add_card_inter B (B'.erase w)
  have hinterle : (B ∩ B'.erase w).card ≤ (B'.erase w).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hinter : 0 < (B ∩ B'.erase w).card := by
    rcases hold with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hnew with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hinter
  obtain ⟨hyB, hyB'e⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyw, hyB'⟩ := Finset.mem_erase.mp hyB'e
  have hNy : A.erase u ∪ A' ⊆ H.neighborFinset y := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hx with hxA | hxA'
    · obtain ⟨hxu, hxA⟩ := Finset.mem_erase.mp hxA
      rcases hcross x hxA y hyB with ⟨h, -⟩ | h
      · exact absurd h hxu
      · exact h.symm
    · rcases hcross' x hxA' y hyB' with ⟨-, h⟩ | h
      · exact absurd h hyw
      · exact h.symm
  have hcardNy := Finset.card_le_card hNy
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcardNy
  have hdegy := hmax y
  have hAe : (A.erase u).card = A.card - 1 := Finset.card_erase_of_mem hu
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hui2 := Finset.card_union_add_card_inter (A.erase u) A'
  by_cases hex : ∃ x0 ∈ A.erase u ∩ A', x0 ≠ a
  · obtain ⟨x0, hx0, hx0a⟩ := hex
    obtain ⟨hx0Ae, hx0A'⟩ := Finset.mem_inter.mp hx0
    obtain ⟨hx0u, hx0A⟩ := Finset.mem_erase.mp hx0Ae
    -- x0 sees all of B and all of B'
    have hNx : insert w (B ∪ B'.erase w) ⊆ H.neighborFinset x0 := by
      intro z hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rcases hcross' x0 hx0A' z hw' with ⟨h, -⟩ | h
        · exact absurd h hx0a
        · exact h
      rcases Finset.mem_union.mp hz with hzB | hzB'
      · rcases hcross x0 hx0A z hzB with ⟨h, -⟩ | h
        · exact absurd h hx0u
        · exact h
      · obtain ⟨-, hzB'⟩ := Finset.mem_erase.mp hzB'
        rcases hcross' x0 hx0A' z hzB' with ⟨h, -⟩ | h
        · exact absurd h hx0a
        · exact h
    have hwnot : w ∉ B ∪ B'.erase w := by
      simp [hwB]
    have hcardNx := Finset.card_le_card hNx
    rw [Finset.card_insert_of_notMem hwnot, SimpleGraph.card_neighborFinset_eq_degree] at hcardNx
    have hdegx := hmax x0
    -- the overlap has at most two vertices: a and one neighbour of w
    have hsub : A.erase u ∩ A' ⊆ insert a ((A.erase u).filter (fun x => H.Adj w x)) := by
      intro x hx
      obtain ⟨hxAe, hxA'⟩ := Finset.mem_inter.mp hx
      rw [Finset.mem_insert, Finset.mem_filter]
      by_cases hxa : x = a
      · exact Or.inl hxa
      · right
        refine ⟨hxAe, ?_⟩
        rcases hcross' x hxA' w hw' with ⟨h, -⟩ | h
        · exact absurd h hxa
        · exact h.symm
    have hov := le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
    rcases hold with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hnew with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · push Not at hex
    have hsub : A.erase u ∩ A' ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (hex x hx)
    have hov := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hov
    rcases hold with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hnew with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
