import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlotsCard
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_probe_tail_count_zero_of_lt_strict

Topic: data_structures   Node: 7327a7ca0a19

Provenance: helper lemma. step towards prime_fixed_offset_linear_probe_stochastic_maximum

For any table size n with [NeZero n], any bijective offset sequence r, and load t < n, the probe tail count is 0 whenever k > t.
-/

/-- For any table size n with [NeZero n], any bijective offset sequence r, and load t < n, the probe tail count is 0 whenever k exceeds t. -/
theorem hash_probe_tail_count_zero_of_lt_strict
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr : Function.Bijective r)
    (t k : ℕ) (ht : t < n) (hkt : t < k) :
    hash_probe_tail_count n r t k = 0 := by
  dsimp [hash_probe_tail_count]
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro p _ hp
  have hS_card : (hash_occupied_slots n r (List.ofFn p.1)).card = t := by
    have hlen : (List.ofFn p.1).length ≤ n := by
      rw [List.length_ofFn]
      omega
    have h := hash_occupied_slots_card n r hr (List.ofFn p.1) hlen
    rw [List.length_ofFn] at h
    exact h
  let f : Fin (t + 1) → ZMod n := fun j =>
    p.2 + r ⟨j.val, by omega⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have h1 : r ⟨a.val, by omega⟩ = r ⟨b.val, by omega⟩ := add_left_cancel hab
    have h2 : (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ := hr.1 h1
    ext
    exact Fin.mk.inj h2
  have hf_sub : ∀ j : Fin (t + 1), f j ∈ hash_occupied_slots n r (List.ofFn p.1) := by
    intro j
    dsimp [f]
    have hj : (⟨j.val, by omega⟩ : Fin n).val < k := by
      have := j.isLt
      dsimp
      omega
    exact hp ⟨j.val, by omega⟩ hj
  have h_image : Finset.image f Finset.univ ⊆ hash_occupied_slots n r (List.ofFn p.1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨j, _, rfl⟩
    exact hf_sub j
  have h_card_le := Finset.card_le_card h_image
  rw [Finset.card_image_of_injective Finset.univ hf_inj] at h_card_le
  rw [Finset.card_fin] at h_card_le
  rw [hS_card] at h_card_le
  omega
