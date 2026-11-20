import AFTD.Prelude

/-!
# bridge_opposite_shore_has_two_external_vertices

Topic: graphs   Node: b5ccf8001290

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family; no first zero-codegree witness required.

Every opposite shore contains at least two external vertices.
-/

theorem bridge_opposite_shore_has_two_external_vertices {V : Type*} [DecidableEq V]
    (S C Q W : Finset V) (d : ℕ) (hSC : Disjoint S C) (hQW : Disjoint Q W)
    (hQ : Q ⊆ S ∪ C) (hW : W ⊆ S) (hS : S.card+1=d)
    (hsize : Q.card+W.card=d+1) : 2 ≤ (Q ∩ C).card := by
  classical
  have hQSpart : Disjoint (Q ∩ S) W := by
    apply Finset.disjoint_left.mpr
    intro a ha hw
    exact (Finset.disjoint_left.mp hQW) (Finset.mem_inter.mp ha).1 hw
  have hQSunion : Q ∩ S ∪ W ⊆ S := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_inter.mp ha).2
    · exact hW ha
  have hle := Finset.card_le_card hQSunion
  rw [Finset.card_union_of_disjoint hQSpart] at hle
  have hdis : Disjoint (Q ∩ S) (Q ∩ C) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hunion : Q ∩ S ∪ Q ∩ C = Q := by
    ext a
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · intro h
      exact h.elim And.left And.left
    · intro ha
      rcases Finset.mem_union.mp (hQ ha) with hs | hc
      · exact Or.inl ⟨ha,hs⟩
      · exact Or.inr ⟨ha,hc⟩
  have hcard : (Q ∩ S).card + (Q ∩ C).card = Q.card := by
    have h := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdis] at h
    exact h
  omega
