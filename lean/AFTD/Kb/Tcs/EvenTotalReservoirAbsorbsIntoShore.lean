import AFTD.Prelude

/-!
# even_total_reservoir_absorbs_into_shore

Topic: graphs   Node: 2a029708cbdd

Provenance: helper lemma. OP-1957; saturated barrier graph-to-count reduction.

In the displayed even-size union of two odd shores and an anticomplete reservoir, the reservoir may be absorbed into the second shore while preserving oddness, total size and the unique crossing-edge condition.
-/

theorem even_total_reservoir_absorbs_into_shore
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X Y U : Finset V) (x y : V) (k : ℕ)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hsize : X.card+Y.card+U.card=2*k)
    (hx : x ∈ X) (hy : y ∈ Y)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ a ∈ U, ∀ b ∈ X, ¬ G.Adj a b)
    (hoddX : Odd X.card) (hoddY : Odd Y.card) :
    Disjoint X (Y ∪ U) ∧ X.card+(Y ∪ U).card=2*k ∧
    x ∈ X ∧ y ∈ Y ∪ U ∧ Odd (Y ∪ U).card ∧
    (∀ a ∈ X, ∀ b ∈ Y ∪ U, G.Adj a b → a=x ∧ b=y) := by
  classical
  have hu : Even U.card := by
    obtain ⟨a,ha⟩ := hoddX
    obtain ⟨b,hb⟩ := hoddY
    rcases Nat.even_or_odd U.card with h | h
    · exact h
    · obtain ⟨c,hc⟩ := h
      omega
  have hyu : Odd (Y ∪ U).card := by
    rw [Finset.card_union_of_disjoint hYU]
    exact hoddY.add_even hu
  have hsz : X.card+(Y ∪ U).card=2*k := by
    rw [Finset.card_union_of_disjoint hYU]
    omega
  refine ⟨?_,hsz,hx,Finset.mem_union_left U hy,hyu,?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hzx hz
    rcases Finset.mem_union.mp hz with hzy | hzu
    · exact Finset.disjoint_left.mp hXY hzx hzy
    · exact Finset.disjoint_left.mp hXU hzx hzu
  · intro a ha b hb hab
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hcross a ha b hb hab
    · exact False.elim (hanti b hb a ha hab.symm)
