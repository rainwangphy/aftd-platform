import AFTD.Prelude

/-!
# op1957_outer_shore_defect_pair

Topic: graphs   Node: aa3e827e9838

Provenance: helper lemma. OP-1957 large-shore defect extraction

If the first shore contains x and at least two further A vertices, and one of p,q lies in the second shore or its anticomplete pool, two A vertices are simultaneous nonneighbors of the root y and that p or q.
-/

theorem op1957_outer_shore_defect_pair
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A X Y U : Finset V) (x y p q : V)
    (hxA : x ∈ A) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hlarge : 3 ≤ (X ∩ A).card)
    (houtside : p ∈ Y ∪ U ∨ q ∈ Y ∪ U) :
    ∃ r ∈ ({p,q} : Finset V), ∃ T ⊆ A.erase x, T.card=2 ∧
      ∀ a ∈ T, ¬ G.Adj a y ∧ ¬ G.Adj a r := by
  classical
  have hx : x ∈ X ∩ A := Finset.mem_inter.mpr ⟨hxX,hxA⟩
  have hc : 2 ≤ ((X ∩ A).erase x).card := by
    have h := Finset.card_erase_add_one hx
    omega
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hc
  obtain ⟨r,hr,hrout⟩ : ∃ r ∈ ({p,q} : Finset V), r ∈ Y ∪ U := by
    rcases houtside with hp | hq
    · exact ⟨p,by simp,hp⟩
    · exact ⟨q,by simp,hq⟩
  refine ⟨r,hr,T,?_,hcard,?_⟩
  · intro a ha
    have hh := Finset.mem_erase.mp (hT ha)
    exact Finset.mem_erase.mpr ⟨hh.1,(Finset.mem_inter.mp hh.2).2⟩
  · intro a ha
    have hh := Finset.mem_erase.mp (hT ha)
    have haX := (Finset.mem_inter.mp hh.2).1
    have hne : a ≠ x := hh.1
    constructor
    · intro hay
      exact hne (hcross a haX y hyY hay).1
    · intro har
      rcases Finset.mem_union.mp hrout with hrY | hrU
      · exact hne (hcross a haX r hrY har).1
      · exact hantiX a haX r hrU har
