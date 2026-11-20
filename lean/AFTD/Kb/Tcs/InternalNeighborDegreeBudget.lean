import AFTD.Prelude

/-!
# internal_neighbor_degree_budget

Topic: graphs   Node: 968195e40d9a

Provenance: helper lemma. OP-1957 saturated-twin bridge-family walk count; scratch Lean axiom audit completed.

A twin-adjacent internal vertex has at most d minus two minus its internal degree external neighbors.
-/

theorem internal_neighbor_degree_budget
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y q : V) (hxy : x ≠ y) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hq : q ∈ S)
    (hSxy : ∀ a ∈ S, H.Adj a x ∧ H.Adj a y)
    (hmax : (H.neighborFinset q).card ≤ d) :
    ((H.neighborFinset q) ∩ S).card + ((H.neighborFinset q) ∩ C).card + 2 ≤ d := by
  classical
  let A := (H.neighborFinset q) ∩ S
  let B := (H.neighborFinset q) ∩ C
  have hxS : x ∉ S := by
    intro hx
    exact (hSxy x hx).1.ne rfl
  have hyS : y ∉ S := by
    intro hy
    exact (hSxy y hy).2.ne rfl
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hxAB : x ∉ A ∪ B := by simp [A,B,hxS,hxC]
  have hyAB : y ∉ A ∪ B := by simp [A,B,hyS,hyC]
  have hxnot : x ∉ insert y (A ∪ B) := by simp [hxy,hxAB]
  have hsub : insert x (insert y (A ∪ B)) ⊆ H.neighborFinset q := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_union] at ha
    rcases ha with rfl | rfl | ha | ha
    · simpa using (hSxy q hq).1
    · simpa using (hSxy q hq).2
    · exact (Finset.mem_inter.mp ha).1
    · exact (Finset.mem_inter.mp ha).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hyAB,
      Finset.card_union_of_disjoint hd] at hc
  have := le_trans hc hmax
  dsimp [A,B] at *
  omega
