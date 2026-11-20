import AFTD.Prelude

/-!
# graph_two_balanced_bridge_complements_degree_obstruction

Topic: graphs   Node: 4d986cf9ac92

Provenance: helper lemma. OP-1957: finite-set counting core for the odd-parameter surplus bound; experiment 34680 tests j=5,...,9 without a second residual minimum-degree condition.

Two balanced bridge-complement configurations cannot coexist under the displayed maximum-degree, cross-adjacency and endpoint-avoidance conditions, for any j at least five.
-/

theorem graph_two_balanced_bridge_complements_degree_obstruction
    (n j : ℕ) (hj : 5 ≤ j) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hmax : ∀ x, H.degree x ≤ j+1)
    (A B A' B' : Finset (Fin n))
    (hAB : Disjoint A B) (hAB' : Disjoint A' B')
    (hA : A.card = j) (hB : B.card = j) (hA' : A'.card = j) (hB' : B'.card = j)
    (u v a w : Fin n) (hu : u ∈ A) (hv : v ∈ B) (huv : ¬ H.Adj u v) (ha : a ∈ A) (hau : a ≠ u)
    (hwA : w ∉ A) (hwB : w ∉ B) (ha' : a ∈ A') (hw' : w ∈ B')
    (hcross : ∀ x ∈ A, ∀ y ∈ B, (x = u ∧ y = v) ∨ H.Adj x y)
    (hcross' : ∀ x ∈ A', ∀ y ∈ B', (x = a ∧ y = w) ∨ H.Adj x y)
    (havoid : ∀ x ∈ A, x ≠ u → ¬ H.Adj w x) : False := by
  classical
  -- the neighbourhood of a contains B and B' minus w
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
  have hEr : (B'.erase w).card = j - 1 := by rw [Finset.card_erase_of_mem hw', hB']
  have hui := Finset.card_union_add_card_inter B (B'.erase w)
  have hinter : 0 < (B ∩ B'.erase w).card := by omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hinter
  obtain ⟨hyB, hyB'e⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyw, hyB'⟩ := Finset.mem_erase.mp hyB'e
  -- the neighbourhood of y contains A minus u and A'
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
  have hsmall : (A.erase u ∩ A').card ≤ 1 := by
    have hsub : A.erase u ∩ A' ⊆ {a} := by
      intro x hx
      obtain ⟨hxAe, hxA'⟩ := Finset.mem_inter.mp hx
      obtain ⟨hxu, hxA⟩ := Finset.mem_erase.mp hxAe
      rw [Finset.mem_singleton]
      by_contra hxa
      rcases hcross' x hxA' w hw' with ⟨h, -⟩ | h
      · exact hxa h
      · exact havoid x hxA hxu h.symm
    simpa using Finset.card_le_card hsub
  have hcardNy := Finset.card_le_card hNy
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcardNy
  have hdegy := hmax y
  have hAe : (A.erase u).card = j - 1 := by rw [Finset.card_erase_of_mem hu, hA]
  have hui2 := Finset.card_union_add_card_inter (A.erase u) A'
  omega
