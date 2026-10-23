import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPhiEntry
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocatedCardLe
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.Tcs.G

/-!
# picking_phi_entry_le

Topic: fair_division   Node: 66b58fefc7b8

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

For the Round-Robin sequence of n agents and m goods, the 0-based rank phi_s of the item selected at turn s is at most s (the paper's 1 <= phi_s <= s, one-based).
-/

/-- If some element of the prefix `l.take k` satisfies the Boolean predicate `p`, then `l.find? p`
returns an element lying in that same prefix. -/
lemma picking_phi_entry_le_find_mem_take {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (k : ℕ), (∃ x ∈ l.take k, p x = true) →
      ∃ g, l.find? p = some g ∧ g ∈ l.take k := by
  intro l
  induction l with
  | nil => intro k h; obtain ⟨x, hx, -⟩ := h; simp at hx
  | cons a as ih =>
    intro k h
    cases k with
    | zero => obtain ⟨x, hx, -⟩ := h; simp at hx
    | succ k' =>
      rw [List.take_succ_cons] at h ⊢
      by_cases hpa : p a = true
      · exact ⟨a, by rw [List.find?_cons, hpa], by simp⟩
      · have hpa' : p a = false := by simpa using hpa
        obtain ⟨x, hx, hpx⟩ := h
        have hx' : x ∈ as.take k' := by
          rcases List.mem_cons.mp hx with h | h
          · subst h; rw [hpa'] at hpx; exact absurd hpx (by simp)
          · exact h
        obtain ⟨g, hg, hmem⟩ := ih k' ⟨x, hx', hpx⟩
        exact ⟨g, by rw [List.find?_cons, hpa']; exact hg, by simp [hmem]⟩

/-- At turn s of Round Robin the selected item's 0-based rank is at most s. -/
theorem picking_phi_entry_le (n : ℕ) [NeZero n] (m : ℕ) (rank : Fin n → Fin m ≃ Fin m) (s : ℕ) :
    picking_phi_entry (round_robin_sequence n m) rank s ≤ s := by
  unfold picking_phi_entry
  split
  · omega
  · rename_i a ha
    have hrr : (round_robin_sequence n m).length = m := by simp [round_robin_sequence]
    have hLlen : (List.ofFn ⇑(rank a)).length = m := List.length_ofFn
    have hslen : s < m := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      omega
    have hLnodup : (List.ofFn ⇑(rank a)).Nodup := by
      rw [List.nodup_ofFn]; exact (rank a).injective
    have hwit : ∃ x ∈ (List.ofFn ⇑(rank a)).take (s + 1),
        (fun g => decide (g ∉ (picking_prefix_state (round_robin_sequence n m) rank s).2)) x = true := by
      by_contra h
      push Not at h
      have hsubset : ((List.ofFn ⇑(rank a)).take (s + 1)).toFinset ⊆
          (picking_prefix_state (round_robin_sequence n m) rank s).2 := by
        intro x hx
        rw [List.mem_toFinset] at hx
        have hx' := h x hx
        simpa using hx'
      have hcard : ((List.ofFn ⇑(rank a)).take (s + 1)).toFinset.card = s + 1 := by
        rw [List.toFinset_card_of_nodup ((List.take_sublist (s+1) _).nodup hLnodup),
          List.length_take, hLlen]
        omega
      have h2 := picking_prefix_state_allocated_card_le (round_robin_sequence n m) rank s
      have h3 := Finset.card_le_card hsubset
      omega
    obtain ⟨g, hfind, hmem⟩ := picking_phi_entry_le_find_mem_take _ _ _ hwit
    rw [hfind]
    simp only
    obtain ⟨i, hi, hig⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take, hLlen] at hi
    have him : i < m := by omega
    rw [List.getElem_take] at hig
    rw [List.getElem_ofFn] at hig
    have hval : (rank a).symm g = ⟨i, him⟩ := by
      rw [← hig]
      exact Equiv.symm_apply_apply (rank a) ⟨i, him⟩
    rw [hval]
    show i ≤ s
    omega
