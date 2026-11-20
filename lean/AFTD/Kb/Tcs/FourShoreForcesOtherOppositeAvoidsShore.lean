import AFTD.Prelude

/-!
# four_shore_forces_other_opposite_avoids_shore

Topic: graphs   Node: f5585da5c01e

Provenance: helper lemma. OP-1957 d=11 bridge-family structural restriction; scratch Lean axiom audit completed.

A saturated four-shore with at most two internal opposite vertices is disjoint from every other opposite shore of size at least four.
-/

theorem four_shore_forces_other_opposite_avoids_shore
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S A B U W : Finset V)
    (hA : A ⊆ S) (hW : W ⊆ S) (hBcard : B.card=8)
    (hWcard : 4 ≤ W.card) (hBS : (B ∩ S).card ≤ 2)
    (hxB : x ∉ B) (hyB : y ∉ B)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, H.Adj u w) : Disjoint A U := by
  classical
  apply Finset.disjoint_left.mpr
  intro a haA haU
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
