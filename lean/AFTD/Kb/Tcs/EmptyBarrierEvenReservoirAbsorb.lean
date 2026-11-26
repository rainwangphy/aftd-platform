import AFTD.Prelude

/-!
# empty_barrier_even_reservoir_absorb

Topic: graphs   Node: e117afc7e6f2

Provenance: helper lemma. OP-1957; forced-edge saturated barrier reduction.

For two odd anticomplete shores with a single permitted crossing edge and an anticomplete reservoir whose union has even size, absorbing the reservoir into the second shore preserves its odd cardinality and the crossing property.
-/

theorem empty_barrier_even_reservoir_absorb
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y U : Finset V) (x y : V)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hcover : X ∪ Y ∪ U = Finset.univ)
    (hx : x ∈ X) (hy : y ∈ Y)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ a ∈ U, ∀ b ∈ X, ¬ G.Adj a b)
    (hoddX : Odd X.card) (hoddY : Odd Y.card)
    (heven : Even (Fintype.card V)) :
    Disjoint X (Y ∪ U) ∧ X ∪ (Y ∪ U) = Finset.univ ∧
    x ∈ X ∧ y ∈ Y ∪ U ∧ Odd (Y ∪ U).card ∧
    (∀ a ∈ X, ∀ b ∈ Y ∪ U, G.Adj a b → a=x ∧ b=y) := by
  classical
  have hXYU : Disjoint (X ∪ Y) U := by
    apply Finset.disjoint_left.mpr
    intro z hz hzu
    rcases Finset.mem_union.mp hz with hzx | hzy
    · exact Finset.disjoint_left.mp hXU hzx hzu
    · exact Finset.disjoint_left.mp hYU hzy hzu
  have hcard : X.card + Y.card + U.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hXY, ← Finset.card_union_of_disjoint hXYU, hcover, Finset.card_univ]
  have hu : Even U.card := by
    obtain ⟨m, hm⟩ := heven
    obtain ⟨a, ha⟩ := hoddX
    obtain ⟨b, hb⟩ := hoddY
    rcases Nat.even_or_odd U.card with h | h
    · exact h
    · obtain ⟨c,hc⟩ := h
      omega
  have hyu : Odd (Y ∪ U).card := by
    rw [Finset.card_union_of_disjoint hYU]
    exact hoddY.add_even hu
  refine ⟨?_, ?_, hx, Finset.mem_union_left U hy, hyu, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hzx hz
    rcases Finset.mem_union.mp hz with hzy | hzu
    · exact Finset.disjoint_left.mp hXY hzx hzy
    · exact Finset.disjoint_left.mp hXU hzx hzu
  · simpa [Finset.union_assoc] using hcover
  · intro a ha b hb hab
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hcross a ha b hb hab
    · exact False.elim (hanti b hb a ha hab.symm)
