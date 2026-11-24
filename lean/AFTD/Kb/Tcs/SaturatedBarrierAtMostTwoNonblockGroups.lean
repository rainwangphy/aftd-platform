import AFTD.Prelude

/-!
# saturated_barrier_at_most_two_nonblock_groups

Topic: graphs   Node: 54de62be6e3d

Provenance: helper lemma. OP-1957, grouped essential-edge barrier

In the displayed saturated four-block setting, at most two pairwise disjoint groups in a shore anticomplete to the distinguished vertex can contain vertices outside B.
-/

private theorem in1158_local_saturated_vertex_shore
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B C D X U : Finset V) (x p q : V)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hx : x ∈ X) (hUX : Disjoint U X)
    (hanti : ∀ u ∈ U, ∀ v ∈ X, ¬ G.Adj u v)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y) :
    U ⊆ B ∪ {p,q} := by
  classical
  intro u hu
  have hux : u ≠ x := by
    intro e
    subst u
    exact Finset.disjoint_left.mp hUX hu hx
  have hna : ¬ G.Adj u x := hanti u hu x hx
  have hucover : u ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
  simp only [Finset.mem_union] at hucover
  rcases hucover with ((ha | hb) | hc) | hd
  · exact False.elim (hna (hsatA u ha hux).symm)
  · exact Finset.mem_union_left _ hb
  · by_cases hp : u = p
    · simp [hp]
    · by_cases hq : u = q
      · simp [hq]
      · exact False.elim (hna (hfull u hc hp hq).symm)
  · exact False.elim (hna (hsatD u hd).symm)


private theorem in1158_local_groups_meeting_set
    {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (I : Finset ι) (F : ι → Finset V) (W : Finset V)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)) :
    (I.filter (fun i => (F i ∩ W).Nonempty)).card ≤ W.card := by
  classical
  let J := I.filter (fun i => (F i ∩ W).Nonempty)
  have hp : (J : Set ι).PairwiseDisjoint (fun i => F i ∩ W) := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (hdis i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij))
  have hs : J.card ≤ ∑ i ∈ J, (F i ∩ W).card := by
    calc
      J.card = ∑ _i ∈ J, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ J, (F i ∩ W).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hi).2
  have hu : J.biUnion (fun i => F i ∩ W) ⊆ W := by
    intro v hv
    obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_inter.mp hv).2
  rw [← Finset.card_biUnion hp] at hs
  exact le_trans hs (Finset.card_le_card hu)

theorem saturated_barrier_at_most_two_nonblock_groups
    {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) (A B C D X U : Finset V) (x p q : V)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hx : x ∈ X) (hUX : Disjoint U X)
    (hanti : ∀ u ∈ U, ∀ v ∈ X, ¬ G.Adj u v)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y)
    (I : Finset ι) (F : ι → Finset V)
    (hsub : ∀ i ∈ I, F i ⊆ U)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j)) :
    (I.filter (fun i => (F i \ B).Nonempty)).card ≤ 2 := by
  classical
  have hU := in1158_local_saturated_vertex_shore G A B C D X U x p q
    hcover hx hUX hanti hsatA hsatD hfull
  have hs : I.filter (fun i => (F i \ B).Nonempty) ⊆
      I.filter (fun i => (F i ∩ {p,q}).Nonempty) := by
    intro i hi
    obtain ⟨hiI,hi⟩ := Finset.mem_filter.mp hi
    obtain ⟨v,hv⟩ := hi
    have hvB := (Finset.mem_sdiff.mp hv).2
    have hv := (Finset.mem_sdiff.mp hv).1
    have hvpair : v ∈ ({p,q} : Finset V) := by
      have hh := hU (hsub i hiI hv)
      rcases Finset.mem_union.mp hh with hB | hpair
      · exact False.elim (hvB hB)
      · exact hpair
    exact Finset.mem_filter.mpr ⟨hiI,⟨v,Finset.mem_inter.mpr ⟨hv,hvpair⟩⟩⟩
  have hh := in1158_local_groups_meeting_set I F ({p,q} : Finset V) hdis
  have hpq : ({p,q} : Finset V).card ≤ 2 := by
    by_cases h : p=q <;> simp [h]
  exact (Finset.card_le_card hs).trans (hh.trans hpq)
