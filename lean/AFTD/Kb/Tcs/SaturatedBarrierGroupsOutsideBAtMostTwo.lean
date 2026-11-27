import AFTD.Prelude

/-!
# saturated_barrier_groups_outside_b_at_most_two

Topic: graphs   Node: 7bb8b510d99d

Provenance: helper lemma. OP-1957: reduction of positive-barrier components under saturation.

For pairwise disjoint groups inside an anticomplete set U, saturation of x in A and D and all but p,q in C forces at most two groups to meet the complement of B.
-/

theorem saturated_barrier_groups_outside_b_at_most_two
    {I V : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (A B C D U : Finset V) (x p q : V)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hxU : x ∉ U)
    (hanti : ∀ u ∈ U, ¬ G.Adj x u)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z)
    (K : Finset I) (F : I → Finset V)
    (hsub : ∀ i ∈ K, F i ⊆ U)
    (hdis : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (F i) (F j)) :
    (K.filter (fun i => (F i \ B).Nonempty)).card ≤ 2 := by
  classical
  have hregion : ∀ u ∈ U, u ∉ B → u ∈ ({p,q} : Finset V) := by
    intro u hu hb
    have hc : u ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
    simp only [Finset.mem_union] at hc
    rcases hc with ((ha | hb') | hc) | hd
    · have hne : u ≠ x := by intro he; subst u; exact hxU hu
      exact False.elim (hanti u hu (hsatA u ha hne))
    · exact False.elim (hb hb')
    · by_cases hp : u = p
      · simp [hp]
      · by_cases hq : u = q
        · simp [hq]
        · exact False.elim (hanti u hu (hfull u hc hp hq))
    · exact False.elim (hanti u hu (hsatD u hd))
  let L := K.filter (fun i => (F i \ B).Nonempty)
  have hex : ∀ i ∈ L, ∃ u, u ∈ F i ∧ u ∉ B := by
    intro i hi
    obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨u,(Finset.mem_sdiff.mp hu).1,(Finset.mem_sdiff.mp hu).2⟩
  let f : I → V := fun i => if h : i ∈ L then Classical.choose (hex i h) else p
  have hf : ∀ i ∈ L, f i ∈ F i ∧ f i ∉ B := by
    intro i hi
    simpa [f,hi] using Classical.choose_spec (hex i hi)
  have hle : L.card ≤ ({p,q} : Finset V).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact hregion (f i) (hsub i (Finset.mem_filter.mp hi).1 (hf i hi).1) (hf i hi).2
    · intro i hi j hj hij
      by_contra hne
      have h := Finset.disjoint_left.mp (hdis i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
      exact h (hf i hi).1 (hij ▸ (hf j hj).1)
  calc
    L.card ≤ ({p,q} : Finset V).card := hle
    _ ≤ 2 := Finset.card_le_two
