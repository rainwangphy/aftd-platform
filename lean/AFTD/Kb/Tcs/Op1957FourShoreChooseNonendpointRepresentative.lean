import AFTD.Prelude

/-!
# op1957_four_shore_choose_nonendpoint_representative

Topic: graphs   Node: f9d42dfb3d98

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore choose nonendpoint representative.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_choose_nonendpoint_representative
    {V : Type*} [Fintype V] [DecidableEq V]
    (F B : Fin 4 → Finset V) (x y : V)
    (hBdis : ∀ i j : Fin 4, i ≠ j → Disjoint (B i) (B j))
    (hx : x ∈ B 0) (hy : y ∈ B 2) (j b : Fin 4)
    (hcount : (if (j=0 ∧ b=0) ∨ (j=1 ∧ b=2) then 2 else 1) ≤ (F j ∩ B b).card) :
    ∃ v ∈ F j, v ∈ B b ∧ (j=0 → v≠x) ∧ (j=1 → v≠y) := by
  classical
  have hpos : 1 ≤ (F j ∩ B b).card := by
    split_ifs at hcount <;> omega
  by_cases h0 : j=0
  · subst j
    by_cases hxW : x ∈ F 0 ∩ B b
    · have hb0 : b=0 := by
        by_contra hn
        exact Finset.disjoint_left.mp (hBdis 0 b (Ne.symm hn)) hx (Finset.mem_inter.mp hxW).2
      subst b
      have htwo : 2 ≤ (F 0 ∩ B 0).card := by simpa using hcount
      have hn : 0 < ((F 0 ∩ B 0).erase x).card := by
        rw [Finset.card_erase_of_mem hxW]
        omega
      obtain ⟨v,hv⟩ := Finset.card_pos.mp hn
      have hv' := Finset.mem_erase.mp hv
      exact ⟨v,(Finset.mem_inter.mp hv'.2).1,(Finset.mem_inter.mp hv'.2).2,by simpa using hv'.1⟩
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
      have hvne : v ≠ x := fun h => hxW (h ▸ hv)
      exact ⟨v,(Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2,by simpa using hvne⟩
  · by_cases h1 : j=1
    · subst j
      by_cases hyW : y ∈ F 1 ∩ B b
      · have hb2 : b=2 := by
          by_contra hn
          exact Finset.disjoint_left.mp (hBdis 2 b (Ne.symm hn)) hy (Finset.mem_inter.mp hyW).2
        subst b
        have htwo : 2 ≤ (F 1 ∩ B 2).card := by simpa using hcount
        have hn : 0 < ((F 1 ∩ B 2).erase y).card := by
          rw [Finset.card_erase_of_mem hyW]
          omega
        obtain ⟨v,hv⟩ := Finset.card_pos.mp hn
        have hv' := Finset.mem_erase.mp hv
        exact ⟨v,(Finset.mem_inter.mp hv'.2).1,(Finset.mem_inter.mp hv'.2).2,by simpa using hv'.1⟩
      · obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
        have hvne : v ≠ y := fun h => hyW (h ▸ hv)
        exact ⟨v,(Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2,by simpa using hvne⟩
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
      exact ⟨v,(Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2,by simp [h0,h1]⟩
