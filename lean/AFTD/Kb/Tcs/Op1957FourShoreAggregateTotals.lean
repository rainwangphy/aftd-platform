import AFTD.Prelude

/-!
# op1957_four_shore_aggregate_totals

Topic: graphs   Node: 1e48994d8f00

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore aggregate totals.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_aggregate_totals
    {V : Type*} [Fintype V] [DecidableEq V]
    (F B : Fin 4 → Finset V) (E : Finset V)
    (hFdis : ∀ i j : Fin 4, i ≠ j → Disjoint (F i) (F j))
    (hEdis : ∀ i : Fin 4, Disjoint (F i) E)
    (hBdis : ∀ i j : Fin 4, i ≠ j → Disjoint (B i) (B j))
    (hBcover : (Finset.univ : Finset (Fin 4)).biUnion B = Finset.univ)
    (hEB : E ⊆ B 1) :
    let g : Fin 4 → Fin 4 → ℕ := fun i b => (F i ∩ B b).card
    let tot : Fin 4 → ℕ := fun b => (∑ i : Fin 4, g i b) + (if b=1 then E.card else 0)
    let W := (Finset.univ : Finset (Fin 4)).biUnion F ∪ E
    (∀ b, tot b = (W ∩ B b).card) ∧
    (∀ b, tot b ≤ (B b).card) ∧ (∑ b : Fin 4, tot b) = W.card := by
  classical
  dsimp only
  let W : Finset V := (Finset.univ : Finset (Fin 4)).biUnion F ∪ E
  have hFB : ∀ b, ((Finset.univ : Finset (Fin 4)).biUnion F ∩ B b).card =
      ∑ i : Fin 4, (F i ∩ B b).card := by
    intro b
    have heq : (Finset.univ : Finset (Fin 4)).biUnion F ∩ B b =
        (Finset.univ : Finset (Fin 4)).biUnion (fun i => F i ∩ B b) := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_biUnion,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨⟨i,hi⟩,hb⟩
        exact ⟨i,hi,hb⟩
      · rintro ⟨i,hi,hb⟩
        exact ⟨⟨i,hi⟩,hb⟩
    have hp : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (fun i => F i ∩ B b) := by
      intro i _ j _ hij
      exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hFdis i j hij))
    rw [heq,Finset.card_biUnion hp]
  have hFE : Disjoint ((Finset.univ : Finset (Fin 4)).biUnion F) E := by
    apply Finset.disjoint_left.mpr
    intro v hv he
    obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hEdis i) hvi he
  have hEtot : ∀ b, (E ∩ B b).card = if b=1 then E.card else 0 := by
    intro b
    by_cases h : b=1
    · subst b
      rw [Finset.inter_eq_left.mpr hEB]
      simp
    · have hd : Disjoint E (B b) := Finset.disjoint_of_subset_left hEB (hBdis 1 b (Ne.symm h))
      rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
      simp [h]
  have hWb : ∀ b, (∑ i : Fin 4, (F i ∩ B b).card) + (if b=1 then E.card else 0) = (W ∩ B b).card := by
    intro b
    have hd : Disjoint (((Finset.univ : Finset (Fin 4)).biUnion F) ∩ B b) (E ∩ B b) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hFE)
    have heq : W ∩ B b = (((Finset.univ : Finset (Fin 4)).biUnion F) ∩ B b) ∪ (E ∩ B b) := by
      ext v
      simp [W,or_and_right]
    rw [heq,Finset.card_union_of_disjoint hd,hFB,hEtot]
  have htotal : (∑ b : Fin 4, (W ∩ B b).card) = W.card := by
    have hp : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (fun b => W ∩ B b) := by
      intro i _ j _ hij
      exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right (hBdis i j hij))
    have heq : (Finset.univ : Finset (Fin 4)).biUnion (fun b => W ∩ B b) = W := by
      ext v
      simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_inter]
      constructor
      · rintro ⟨b,hv,_⟩
        exact hv
      · intro hv
        have hh : v ∈ (Finset.univ : Finset (Fin 4)).biUnion B := by rw [hBcover]; simp
        obtain ⟨b,_,hvb⟩ := Finset.mem_biUnion.mp hh
        exact ⟨b,hv,hvb⟩
    rw [← Finset.card_biUnion hp,heq]
  refine ⟨hWb,?_,?_⟩
  · intro b
    rw [hWb b]
    exact Finset.card_le_card Finset.inter_subset_right
  · simp_rw [hWb]
    exact htotal
