import AFTD.Prelude

/-!
# op1957_large_shore_reduction_to_B_only

Topic: graphs   Node: c7dc90c194f5

Provenance: helper lemma. OP-1957 direct large-shore reduction to a B-only positive barrier

In the large-shore case, if the complement of the first shore is supported in B together with p, q and y, then ruling out a B-only barrier when the first shore contains three or four A vertices implies the desired common-defect or all-four-defect alternative.
-/

theorem in1245_outside_C_defect_pair
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

theorem op1957_large_shore_reduction_to_B_only
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B X Y U : Finset V) (x y p q : V)
    (hxA : x ∈ A) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hYU : Disjoint Y U) (hA : A.card=5)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hregion : Y ∪ U ⊆ B ∪ {p,q,y})
    (hlarge : 3 ≤ (X ∩ A).card)
    (hNoPool : Y ⊆ B ∪ {y} → U ⊆ B → (X ∩ A).card ≤ 4 → False) :
    (∃ r ∈ ({p,q} : Finset V), ∃ T ⊆ A.erase x, T.card=2 ∧
      ∀ a ∈ T, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
    (∀ a ∈ A.erase x, ¬ G.Adj a y) := by
  classical
  by_cases hout : p ∈ Y ∪ U ∨ q ∈ Y ∪ U
  · exact Or.inl (in1245_outside_C_defect_pair G A X Y U x y p q hxA hxX hyY hcross hantiX hlarge hout)
  · have hp : p ∉ Y ∪ U := fun h => hout (Or.inl h)
    have hq : q ∉ Y ∪ U := fun h => hout (Or.inr h)
    have hyU : y ∉ U := fun h => Finset.disjoint_left.mp hYU hyY h
    have hY : Y ⊆ B ∪ {y} := by
      intro z hz
      have hz' : z ∈ Y ∪ U := Finset.mem_union_left _ hz
      have h := hregion hz'
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · subst z; exact False.elim (hp hz')
      · subst z; exact False.elim (hq hz')
      · exact Or.inr h
    have hU : U ⊆ B := by
      intro z hz
      have hz' : z ∈ Y ∪ U := Finset.mem_union_right _ hz
      have h := hregion hz'
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h | h | h | h
      · exact h
      · subst z; exact False.elim (hp hz')
      · subst z; exact False.elim (hq hz')
      · subst z; exact False.elim (hyU hz)
    by_cases hs : (X ∩ A).card ≤ 4
    · exact False.elim (hNoPool hY hU hs)
    · have hcard : (X ∩ A).card = A.card := by
        have hh := Finset.card_le_card (Finset.inter_subset_right : X ∩ A ⊆ A)
        omega
      have hsub : A ⊆ X := by
        have heq : X ∩ A = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        intro a ha
        exact (Finset.mem_inter.mp (heq.symm ▸ ha)).1
      right
      intro a ha hay
      have ha' := Finset.mem_erase.mp ha
      exact ha'.1 (hcross a (hsub ha'.2) y hyY hay).1
