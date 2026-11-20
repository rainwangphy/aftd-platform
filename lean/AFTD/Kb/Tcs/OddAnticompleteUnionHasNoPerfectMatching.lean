import AFTD.Prelude

/-!
# odd_anticomplete_union_has_no_perfect_matching

Topic: graphs   Node: 5778e84f5a3a

Provenance: helper lemma. Factor-critical crossing-cut parity ingredient in the OP-1957 campaign.

If two disjoint finite vertex sets are anticomplete and the first has odd size, the graph induced by their union has no perfect matching.
-/

theorem odd_anticomplete_union_has_no_perfect_matching : ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B : Finset V),
    Disjoint A B → Odd A.card →
    (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) →
    ¬ ∃ P : (G.induce {v | v ∈ A ∨ v ∈ B}).Subgraph, P.IsPerfectMatching := by
  intro V instF instD G A B hAB hodd hcross
  classical
  rintro ⟨P, hP⟩
  let C : Set {v : V // v ∈ A ∨ v ∈ B} := {v | v.val ∈ A}
  let R := P.induce C
  have hRmatch : R.IsMatching := by
    intro a ha
    have haA : a.val ∈ A := ha
    obtain ⟨b, hab, huniq⟩ := hP.1 (hP.2 a)
    have hbA : b.val ∈ A := by
      rcases b.property with hbA | hbB
      · exact hbA
      · exact False.elim (hcross a.val haA b.val hbB (P.adj_sub hab))
    refine ⟨b, ⟨haA, hbA, hab⟩, ?_⟩
    intro c hc
    exact huniq c hc.2.2
  let e : R.verts ≃ {v : V // v ∈ A} := {
    toFun := fun ⟨⟨v, hv⟩, ha⟩ => ⟨v, ha⟩
    invFun := fun ⟨v, hv⟩ => ⟨⟨v, Or.inl hv⟩, hv⟩
    left_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro v; apply Subtype.ext; rfl }
  have hcard : R.verts.toFinset.card = A.card := by
    rw [Set.toFinset_card]
    have he := Fintype.card_congr e
    simpa using he
  have heven := hRmatch.even_card
  rw [hcard] at heven
  exact (Nat.not_odd_iff_even.mpr heven) hodd
