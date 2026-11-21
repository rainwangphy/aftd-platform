import AFTD.Prelude

/-!
# d11_disjoint_four_six_shore_bicliques_impossible

Topic: graphs   Node: 5c437c7f6263

Provenance: helper lemma. OP-1957 crossing-shore structural reduction, session IN-1122.

In the displayed degree-eleven configuration, disjoint four- and six-vertex shores cannot have the indicated complete opposite shores when the first opposite shore has one to four internal vertices.
-/

theorem d11_disjoint_four_six_shore_bicliques_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B D Q : Finset V)
    (hS : S.card = 10) (hA : A ⊆ S) (hD : D ⊆ S)
    (hAc : A.card = 4) (hDc : D.card = 6) (hBc : B.card = 8) (hQc : Q.card = 6)
    (hAD : Disjoint A D) (hAB : Disjoint A B) (hDQ : Disjoint D Q)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxB : x ∉ B) (hyB : y ∉ B)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hinner : 1 ≤ (B ∩ S).card ∧ (B ∩ S).card ≤ 4)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hSxy : ∀ v ∈ S, H.Adj v x ∧ H.Adj v y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQD : ∀ q ∈ Q, ∀ a ∈ D, H.Adj q a) : False := by
  classical
  have hpart : A ∪ D = S := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hA hD)
    rw [Finset.card_union_of_disjoint hAD, hAc, hDc, hS]
  have hBD : (B ∩ D).card ≤ 4 := by
    have hsub : B ∩ D ⊆ B ∩ S := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, hD (Finset.mem_inter.mp ha).2⟩
    exact (Finset.card_le_card hsub).trans hinner.2
  have hAQ : Disjoint A Q := by
    apply Finset.disjoint_left.mpr
    intro q hqA hqQ
    have hqx : H.Adj q x := (hSxy q (hA hqA)).1
    have hqy : H.Adj q y := (hSxy q (hA hqA)).2
    have hxD : x ∉ D := fun h => hxS (hD h)
    have hyD : y ∉ D := fun h => hyS (hD h)
    have hxU : x ∉ B ∪ D := by simp [hxB, hxD]
    have hyU : y ∉ B ∪ D := by simp [hyB, hyD]
    have hsub : insert x (insert y (B ∪ D)) ⊆ H.neighborFinset q := by
      intro v hv
      rw [H.mem_neighborFinset]
      simp only [Finset.mem_insert, Finset.mem_union] at hv
      rcases hv with rfl | rfl | hv | hv
      · exact hqx
      · exact hqy
      · exact (hBA v hv q hqA).symm
      · exact hQD q hqQ v hv
    have hn := (Finset.card_le_card hsub).trans (hmax q)
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxU]), Finset.card_insert_of_notMem hyU] at hn
    have hu := Finset.card_inter_add_card_union B D
    omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < (B ∩ S).card)
  have hbB := (Finset.mem_inter.mp hb).1
  have hbS := (Finset.mem_inter.mp hb).2
  have hbD : b ∈ D := by
    have hbU : b ∈ A ∪ D := by rwa [hpart]
    rcases Finset.mem_union.mp hbU with hbA | hbD
    · exact False.elim ((Finset.disjoint_left.mp hAB) hbA hbB)
    · exact hbD
  have hbx : H.Adj b x := (hSxy b hbS).1
  have hby : H.Adj b y := (hSxy b hbS).2
  have hxA : x ∉ A := fun h => hxS (hA h)
  have hyA : y ∉ A := fun h => hyS (hA h)
  have hxU : x ∉ A ∪ Q := by simp [hxQ, hxA]
  have hyU : y ∉ A ∪ Q := by simp [hyQ, hyA]
  have hsub : insert x (insert y (A ∪ Q)) ⊆ H.neighborFinset b := by
    intro v hv
    rw [H.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with rfl | rfl | hv | hv
    · exact hbx
    · exact hby
    · exact hBA b hbB v hv
    · exact (hQD v hv b hbD).symm
  have hn := (Finset.card_le_card hsub).trans (hmax b)
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxU]), Finset.card_insert_of_notMem hyU,
    Finset.card_union_of_disjoint hAQ, hAc, hQc] at hn
  omega
