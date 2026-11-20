import AFTD.Prelude

/-!
# external_neighbor_count_at_most_degree_sub_three

Topic: graphs   Node: d909ca638562

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family, without the first zero-codegree witness.

The complement degree bound leaves at most d−3 external neighbors in the displayed first-shore configuration.
-/

theorem external_neighbor_count_at_most_degree_sub_three
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y w q : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hw : w ∈ S)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y) (hqw : H.Adj q w)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hqtype : q ∈ S ∨ (q ∈ C ∧ 3 ≤ ((H.neighborFinset q) ∩ S).card)) :
    ((H.neighborFinset q) ∩ C).card ≤ d-3 := by
  classical
  rcases hqtype with hqS | ⟨hqC,hqS3⟩
  · let U := (H.neighborFinset q) ∩ C
    have hwC : w ∉ C := fun h => (Finset.disjoint_left.mp hSC) hw h
    have hxU : x ∉ U := by simp [U,hxC]
    have hyU : y ∉ U := by simp [U,hyC]
    have hwU : w ∉ U := by simp [U,hwC]
    have hxw : x ≠ w := (hSxy w hw).1.ne.symm
    have hyw : y ≠ w := (hSxy w hw).2.ne.symm
    have hxnot : x ∉ insert y (insert w U) := by simp [hxy,hxw,hxU]
    have hynot : y ∉ insert w U := by simp [hyw,hyU]
    have hsub : insert x (insert y (insert w U)) ⊆ H.neighborFinset q := by
      intro a ha
      rw [H.mem_neighborFinset]
      simp only [Finset.mem_insert] at ha
      rcases ha with rfl | rfl | rfl | ha
      · exact (hSxy q hqS).1
      · exact (hSxy q hqS).2
      · exact hqw
      · exact (H.mem_neighborFinset q a).mp (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hynot,
      Finset.card_insert_of_notMem hwU] at hc
    have hc' := le_trans hc hmax
    dsimp [U] at hc'
    omega
  · let A := (H.neighborFinset q) ∩ S
    let B := (H.neighborFinset q) ∩ C
    have hdis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have hsub : A ∪ B ⊆ H.neighborFinset q := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_inter.mp ha).1
      · exact (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at hc
    have hc' := le_trans hc hmax
    dsimp [A,B] at hc'
    omega
