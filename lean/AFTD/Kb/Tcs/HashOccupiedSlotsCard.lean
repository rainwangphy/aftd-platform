import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.HashOccupiedSlotsNil
import AFTD.Kb.Tcs.HashInsertStep

/-!
# hash_occupied_slots_card

Topic: data_structures   Node: 64da8d677a9a

Provenance: helper lemma. step towards unit_first_fixed_offset_mean_probe_maximum

For any table size n with [NeZero n], any bijective offset sequence r : Fin n → ZMod n, and any list of keys A with length at most n, the set of occupied slots hash_occupied_slots n r A has cardinality equal to A.length.
-/

lemma hash_occupied_slots_card_insert_step (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (T : Finset (ZMod n)) (hT : T.card < n) (a : ZMod n) :
    (hash_insert_step n r T a).card = T.card + 1 := by
  have h_cand : (Finset.univ.filter (fun j : Fin n => a + r j ∉ T)).Nonempty := by
    have h_inj : Function.Injective (fun j : Fin n => a + r j) := by
      have : (fun j : Fin n => a + r j) = (fun x : ZMod n => a + x) ∘ r := rfl
      rw [this]
      exact (AddGroup.addLeft_bijective a).injective.comp hr.injective
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_all : ∀ j : Fin n, a + r j ∈ T := by
      intro j
      by_contra hj
      have : j ∈ Finset.univ.filter (fun j : Fin n => a + r j ∉ T) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hj⟩
      rw [h_empty] at this
      exact Finset.notMem_empty j this
    have h_sub : (Finset.univ.image (fun j : Fin n => a + r j)) ⊆ T := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨j, _, rfl⟩
      exact h_all j
    have h_card_le : (Finset.univ.image (fun j : Fin n => a + r j)).card ≤ T.card :=
      Finset.card_le_card h_sub
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_univ, Fintype.card_fin] at h_card_le
    omega
  unfold hash_insert_step
  dsimp
  rw [dif_pos h_cand]
  rw [Finset.union_comm, Finset.singleton_union, Finset.card_insert_of_notMem]
  have h_min := Finset.min'_mem (Finset.univ.filter fun j => a + r j ∉ T) h_cand
  rw [Finset.mem_filter] at h_min
  exact h_min.2

/-- Inserting a sequence of length at most n into an initially empty table always occupies exactly as many slots as inserted keys. -/
theorem hash_occupied_slots_card (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (A : List (ZMod n)) (hA : A.length ≤ n) :
    (hash_occupied_slots n r A).card = A.length := by
  induction A using List.reverseRecOn with
  | nil =>
    rw [hash_occupied_slots_nil, Finset.card_empty, List.length_nil]
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton] at hA ⊢
    have h_xs_len : xs.length ≤ n := by omega
    have ih_val := ih h_xs_len
    have h_fold : hash_occupied_slots n r (xs ++ [x]) =
        hash_insert_step n r (hash_occupied_slots n r xs) x := by
      dsimp [hash_occupied_slots]
      rw [List.foldl_append]
      rfl
    rw [h_fold]
    rw [hash_occupied_slots_card_insert_step n r hr (hash_occupied_slots n r xs)]
    · rw [ih_val]
    · rw [ih_val]
      omega
