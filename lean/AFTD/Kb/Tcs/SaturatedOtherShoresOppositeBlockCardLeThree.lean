import AFTD.Prelude

/-!
# saturated_other_shores_opposite_block_card_le_three

Topic: graphs   Node: d053764ad601

Provenance: helper lemma. OP-1957; saturated positive-barrier graph-to-count transfer.

For disjoint shores with only the displayed crossing edge, saturation at x limits the total number of C vertices on the other three shores to three.
-/

set_option maxHeartbeats 2000000

theorem saturated_other_shores_opposite_block_card_le_three
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Fin 4 → Finset V) (C : Finset V) (x y p q : V)
    (hdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hx : x ∈ F 0)
    (hcross : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x))
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z) :
    (F 1 ∩ C).card+(F 2 ∩ C).card+(F 3 ∩ C).card ≤ 3 := by
  classical
  have hallowed : ∀ i : Fin 4, i ≠ 0 → F i ∩ C ⊆ ({p,q,y} : Finset V) := by
    intro i hi z hz
    obtain ⟨hzF,hzC⟩ := Finset.mem_inter.mp hz
    by_cases hp : z=p
    · simp [hp]
    · by_cases hq : z=q
      · simp [hq]
      · have hh := hcross 0 i (Ne.symm hi) x hx z hzF (hfull z hzC hp hq)
        have he : z=y := by
          rcases hh with h | h
          · exact h.2.2.2
          · have : (0 : Fin 4) = 1 := h.1
            exact ((by decide : (0 : Fin 4) ≠ 1) this).elim
        simp [he]
  let P := F 1 ∩ C
  let Q := F 2 ∩ C
  let R := F 3 ∩ C
  have hPQ : Disjoint P Q := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdis 1 2 (by decide)))
  have hPR : Disjoint P R := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdis 1 3 (by decide)))
  have hQR : Disjoint Q R := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdis 2 3 (by decide)))
  have hPQR : Disjoint (P ∪ Q) R := Finset.disjoint_union_left.mpr ⟨hPR,hQR⟩
  have hsub : P ∪ Q ∪ R ⊆ ({p,q,y} : Finset V) := by
    exact Finset.union_subset (Finset.union_subset (hallowed 1 (by decide)) (hallowed 2 (by decide)))
      (hallowed 3 (by decide))
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hPQR,Finset.card_union_of_disjoint hPQ] at hh
  have hs : ({p,q,y} : Finset V).card ≤ 3 := Finset.card_le_three
  dsimp [P,Q,R] at hh
  omega
