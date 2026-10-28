import AFTD.Prelude

/-!
# tree_card_four_iso_of_exists_degree_three

Topic: graphs   Node: b5f4f03e7893

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

Any two trees on 4 vertices each possessing a vertex of degree 3 are isomorphic.
-/

lemma tree_card_four_iso_of_exists_degree_three_aux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 4)
    {v : V} (hdeg : G.degree v = 3) :
    ∀ w : V, w ≠ v → G.Adj v w := by
  intro w hw
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rw [SimpleGraph.mem_neighborFinset] at hu
    exact hu.ne'
  have hcard1 : (Finset.univ.erase v).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    rw [Finset.card_univ, hcard]
  have hcard2 : (G.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  have heq : G.neighborFinset v = Finset.univ.erase v :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2])
  have hw_mem : w ∈ Finset.univ.erase v := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hw
  rw [← heq] at hw_mem
  rwa [SimpleGraph.mem_neighborFinset] at hw_mem

lemma tree_card_four_iso_of_exists_degree_three_no_triangle {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) {v x y : V}
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : G.Adj x y) : False := by
  have hyx := hxy.symm
  obtain ⟨p, hp, huniq⟩ := hG.existsUnique_path v x
  have hp1 : (SimpleGraph.Walk.cons hvx SimpleGraph.Walk.nil).IsPath := by
    simp [hvx.ne]
  have hp2 : (SimpleGraph.Walk.cons hvy (SimpleGraph.Walk.cons hyx SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨by simp [hyx.ne], ?_⟩
    simp [hvy.ne, hvx.ne]
  have e1 := huniq _ hp1
  have e2 := huniq _ hp2
  have hlen : (SimpleGraph.Walk.cons hvx SimpleGraph.Walk.nil).length =
              (SimpleGraph.Walk.cons hvy (SimpleGraph.Walk.cons hyx SimpleGraph.Walk.nil)).length := by
    rw [e1, e2]
  simp at hlen

lemma tree_card_four_iso_of_exists_degree_three_aux_adj {V : Type*} (G : SimpleGraph V)
    (hG : G.IsTree) {v : V} (hv : ∀ w : V, w ≠ v → G.Adj v w) (x y : V) :
    G.Adj x y ↔ x ≠ y ∧ (x = v ∨ y = v) := by
  constructor
  · intro h
    refine ⟨h.ne, ?_⟩
    by_contra hc
    have h1 : x ≠ v := fun hx => hc (Or.inl hx)
    have h2 : y ≠ v := fun hy => hc (Or.inr hy)
    exact tree_card_four_iso_of_exists_degree_three_no_triangle hG (hv x h1) (hv y h2) h
  · rintro ⟨hne, rfl | rfl⟩
    · exact hv y hne.symm
    · exact (hv x hne).symm

/-- Any two trees on 4 vertices each possessing a vertex of degree 3 are isomorphic. -/
theorem tree_card_four_iso_of_exists_degree_three {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
    (T₁ : SimpleGraph V₁) (T₂ : SimpleGraph V₂) [DecidableRel T₁.Adj] [DecidableRel T₂.Adj]
    (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) (hcard₁ : Fintype.card V₁ = 4) (hcard₂ : Fintype.card V₂ = 4)
    (hv₁ : ∃ v : V₁, T₁.degree v = 3) (hv₂ : ∃ v : V₂, T₂.degree v = 3) :
    Nonempty (T₁ ≃g T₂) := by
  obtain ⟨v₁, hv₁⟩ := hv₁
  obtain ⟨v₂, hv₂⟩ := hv₂
  have hadj₁ := tree_card_four_iso_of_exists_degree_three_aux T₁ hcard₁ hv₁
  have hadj₂ := tree_card_four_iso_of_exists_degree_three_aux T₂ hcard₂ hv₂
  have key₁ := tree_card_four_iso_of_exists_degree_three_aux_adj T₁ hT₁ hadj₁
  have key₂ := tree_card_four_iso_of_exists_degree_three_aux_adj T₂ hT₂ hadj₂
  obtain ⟨E⟩ : Nonempty (V₁ ≃ V₂) := by
    rw [← Fintype.card_eq]
    rw [hcard₁, hcard₂]
  have hex : ∀ x : V₁, E.trans (Equiv.swap (E v₁) v₂) x = v₂ ↔ x = v₁ := by
    intro x
    show Equiv.swap (E v₁) v₂ (E x) = v₂ ↔ x = v₁
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right, E.injective.eq_iff]
  have hne : ∀ x y : V₁, (E.trans (Equiv.swap (E v₁) v₂) x
      = E.trans (Equiv.swap (E v₁) v₂) y ↔ x = y) := by
    intro x y
    exact (Equiv.injective _).eq_iff
  refine ⟨RelIso.mk (E.trans (Equiv.swap (E v₁) v₂)) ?_⟩
  intro x y
  rw [key₂, key₁, hex x, hex y, ne_eq, ne_eq, hne x y]
