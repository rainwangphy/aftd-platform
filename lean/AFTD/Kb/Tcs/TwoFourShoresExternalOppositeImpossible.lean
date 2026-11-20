import AFTD.Prelude

/-!
# two_four_shores_external_opposite_impossible

Topic: graphs   Node: 6256ab95b653

Provenance: helper lemma. OP-1957 d=11 bridge-family structural restriction; scratch Lean axiom audit completed.

A four-shore with at most two internal opposite vertices cannot have a second four-shore at a vertex of its opposite shore.
-/

theorem two_four_shores_external_opposite_impossible
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y z : V) (hxy : x ≠ y) (S A B U W : Finset V)
    (hA : A ⊆ S) (hW : W ⊆ S) (hAcard : A.card=4) (hBcard : B.card=8)
    (hUcard : U.card=8) (hWcard : W.card=4) (hBS : (B ∩ S).card ≤ 2)
    (hxB : x ∉ B) (hyB : y ∉ B) (hzB : z ∈ B)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hzU : ∀ u ∈ U, H.Adj z u)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, H.Adj u w) : False := by
  classical
  have hAU : ¬ Disjoint A U := by
    intro hd
    have hsub : A ∪ U ⊆ H.neighborFinset z := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (H.mem_neighborFinset z a).mpr (hBA z hzB a ha)
      · exact (H.mem_neighborFinset z a).mpr (hzU a ha)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd,hAcard,hUcard] at hc
    have hm := hmax z
    omega
  have hi : (A ∩ U).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hAU
  obtain ⟨a,ha⟩ := hi
  have haA : a ∈ A := (Finset.mem_inter.mp ha).1
  have haU : a ∈ U := (Finset.mem_inter.mp ha).2
  have hxS : x ∉ S := by
    intro hx
    exact (hSxy x hx).1.ne rfl
  have hyS : y ∉ S := by
    intro hy
    exact (hSxy y hy).2.ne rfl
  have hxW : x ∉ W := fun h => hxS (hW h)
  have hyW : y ∉ W := fun h => hyS (hW h)
  have hBW : (B ∩ W).card ≤ 2 := by
    have hsub : B ∩ W ⊆ B ∩ S := by
      intro b hb
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).1,hW (Finset.mem_inter.mp hb).2⟩
    exact le_trans (Finset.card_le_card hsub) hBS
  have hBU := Finset.card_union_add_card_inter B W
  have hBUlow : 10 ≤ (B ∪ W).card := by omega
  have hxBU : x ∉ B ∪ W := by simp [hxB,hxW]
  have hyBU : y ∉ B ∪ W := by simp [hyB,hyW]
  have hxnot : x ∉ insert y (B ∪ W) := by simp [hxy,hxBU]
  have hsub : insert x (insert y (B ∪ W)) ⊆ H.neighborFinset a := by
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_union] at hb
    rcases hb with rfl | rfl | hb | hb
    · simpa using (hSxy a (hA haA)).1
    · simpa using (hSxy a (hA haA)).2
    · simpa using (hBA b hb a haA).symm
    · simpa using hUW a haU b hb
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyBU] at hc
  have hm := hmax a
  omega
