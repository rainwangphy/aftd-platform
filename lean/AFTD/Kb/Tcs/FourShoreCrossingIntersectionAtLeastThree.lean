import AFTD.Prelude

/-!
# four_shore_crossing_intersection_at_least_three

Topic: graphs   Node: 5a91af48372b

Provenance: helper lemma. OP-1957 four-shore crossing and repeated-shore analysis; scratch Lean axiom audit completed.

A crossing shore meets a saturated four-shore in at least three vertices.
-/

theorem four_shore_crossing_intersection_at_least_three
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B W Q : Finset V)
    (hA : A ⊆ S) (hAcard : A.card = 4) (hBcard : B.card = 8)
    (hWQsize : W.card + Q.card = 12)
    (hcrossing : (A ∪ W).card + (B ∩ Q).card = 12)
    (hAW : (A ∩ W).Nonempty) (hxB : x ∉ B) (hyB : y ∉ B)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQW : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w) : 3 ≤ (A ∩ W).card := by
  classical
  obtain ⟨a,ha⟩ := hAW
  have haA : a ∈ A := (Finset.mem_inter.mp ha).1
  have haW : a ∈ W := (Finset.mem_inter.mp ha).2
  let D := Q \ B
  have hd : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro z hz hzD
    exact (Finset.mem_sdiff.mp hzD).2 hz
  have hxD : x ∉ D := by simp [D,hxQ]
  have hyD : y ∉ D := by simp [D,hyQ]
  have hxBD : x ∉ B ∪ D := by simp [hxB,hxD]
  have hyBD : y ∉ B ∪ D := by simp [hyB,hyD]
  have hxnot : x ∉ insert y (B ∪ D) := by simp [hxy,hxBD]
  have hsub : insert x (insert y (B ∪ D)) ⊆ H.neighborFinset a := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_union] at hz
    rcases hz with rfl | rfl | hz | hz
    · simpa using (hSxy a (hA haA)).1
    · simpa using (hSxy a (hA haA)).2
    · simpa using (hBA z hz a haA).symm
    · have hzQ := (Finset.mem_sdiff.mp hz).1
      simpa using (hQW z hzQ a haW).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyBD,
    Finset.card_union_of_disjoint hd,hBcard] at hc
  have hm := hmax a
  have hD : D.card ≤ 1 := by omega
  have hAWsum := Finset.card_union_add_card_inter A W
  have hQBsum := Finset.card_sdiff_add_card_inter Q B
  rw [Finset.inter_comm Q B] at hQBsum
  dsimp [D] at hD
  omega
