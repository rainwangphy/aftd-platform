import AFTD.Prelude

/-!
# op309_prefix_counter_clauses

Topic: graphs   Node: 2ff25efc9c4d

Provenance: helper lemma. OP-309 triangle expansion repair obstruction

A finite set of at most two changed positions gives sound one-change and two-change prefix counters, including the clauses excluding a third change.
-/

theorem op309_prefix_counter_clauses {n : ℕ} (bad : Fin n → Prop) [DecidablePred bad]
    (hcard : (Finset.univ.filter bad).card ≤ 2) :
    let one : ℕ → Prop := fun t => ∃ i : Fin n, i.val ≤ t ∧ bad i
    let two : ℕ → Prop := fun t => ∃ i j : Fin n, i.val < j.val ∧ j.val ≤ t ∧ bad i ∧ bad j
    (∀ i : Fin n, bad i → one i.val) ∧
    (∀ t, one t → one (t+1)) ∧
    (∀ i : Fin n, bad i → i.val > 0 → one (i.val-1) → two i.val) ∧
    (∀ t, two t → two (t+1)) ∧
    (∀ i : Fin n, bad i → i.val > 0 → ¬ two (i.val-1)) ∧
    ¬ two 0 := by
  dsimp only
  have no_three (i j k : Fin n) (hij : i.val < j.val) (hjk : j.val < k.val)
      (hi : bad i) (hj : bad j) (hk : bad k) : False := by
    have hij' : i ≠ j := by intro h; subst j; omega
    have hik' : i ≠ k := by intro h; subst k; omega
    have hjk' : j ≠ k := by intro h; subst k; omega
    have hs : ({i,j,k} : Finset (Fin n)) ⊆ Finset.univ.filter bad := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hs
    simp [hij', hik', hjk'] at hc
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact ⟨i, le_rfl, hi⟩
  · intro t ⟨i,hi,hb⟩; exact ⟨i, by omega, hb⟩
  · intro i hi hpos ⟨j,hj,hb⟩; exact ⟨j,i,by omega,le_rfl,hb,hi⟩
  · intro t ⟨i,j,hij,hj,hi,hb⟩; exact ⟨i,j,hij,by omega,hi,hb⟩
  · intro i hi hpos ⟨j,k,hjk,hk,hj,hkb⟩
    exact no_three j k i hjk (by omega) hj hkb hi
  · rintro ⟨i,j,hij,hj,_,_⟩
    omega
