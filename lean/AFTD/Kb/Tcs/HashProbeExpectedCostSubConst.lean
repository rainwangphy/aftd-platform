import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.HashInsertStep
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeTailCount

/-!
# hash_probe_expected_cost_sub_const

Topic: data_structures   Node: 3c98f2c20135

Provenance: helper lemma. step towards fixed_offset_hash_worst_mean_mixed_radix

Translating an offset sequence by subtracting a constant element c in ZMod n preserves the expected probe cost at any load t, by translation equivariance of uniform open addressing.
-/

theorem hash_probe_expected_cost_sub_const_insert_step (n : ℕ) (r : Fin n → ZMod n) (c : ZMod n) (T : Finset (ZMod n)) (a : ZMod n) :
    hash_insert_step n (fun j => r j - c) T a = hash_insert_step n r T (a - c) := by
  dsimp [hash_insert_step]
  simp_rw [show ∀ j : Fin n, a + (r j - c) = a - c + r j from fun j => by ring]

theorem hash_probe_expected_cost_sub_const_occupied_slots_foldl (n : ℕ) (r : Fin n → ZMod n) (c : ZMod n) (A : List (ZMod n)) (T : Finset (ZMod n)) :
    List.foldl (hash_insert_step n (fun j => r j - c)) T A =
    List.foldl (hash_insert_step n r) T (A.map (· - c)) := by
  induction A generalizing T with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [hash_probe_expected_cost_sub_const_insert_step]
    exact ih _

theorem hash_probe_expected_cost_sub_const_occupied_slots (n : ℕ) (r : Fin n → ZMod n) (c : ZMod n) (A : List (ZMod n)) :
    hash_occupied_slots n (fun j => r j - c) A = hash_occupied_slots n r (A.map (· - c)) :=
  hash_probe_expected_cost_sub_const_occupied_slots_foldl n r c A ∅

def hash_probe_expected_cost_sub_const_equiv (t n : ℕ) (c : ZMod n) :
    ((Fin t → ZMod n) × ZMod n) ≃ ((Fin t → ZMod n) × ZMod n) where
  toFun p := (fun i => p.1 i - c, p.2 - c)
  invFun p := (fun i => p.1 i + c, p.2 + c)
  left_inv p := by ext <;> simp only [sub_add_cancel]
  right_inv p := by ext <;> simp only [add_sub_cancel_right]

theorem hash_probe_expected_cost_sub_const_tail_count
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (c : ZMod n) (t k : ℕ) :
    hash_probe_tail_count n (fun j => r j - c) t k = hash_probe_tail_count n r t k := by
  dsimp [hash_probe_tail_count]
  let e := hash_probe_expected_cost_sub_const_equiv t n c
  refine Finset.card_bijective e e.bijective ?_
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h_occ : hash_occupied_slots n (fun j => r j - c) (List.ofFn p.1) =
      hash_occupied_slots n r (List.ofFn (e p).1) := by
    rw [hash_probe_expected_cost_sub_const_occupied_slots]
    congr 1
    dsimp [e, hash_probe_expected_cost_sub_const_equiv]
    simp only [List.map_ofFn]
    rfl
  have h_slot (j : Fin n) : p.2 + (r j - c) = (e p).2 + r j := by
    dsimp [e, hash_probe_expected_cost_sub_const_equiv]
    ring
  simp_rw [h_slot, h_occ]

theorem hash_probe_expected_cost_sub_const_tail_prob
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (c : ZMod n) (t k : ℕ) :
    hash_probe_tail_prob n (fun j => r j - c) t k = hash_probe_tail_prob n r t k := by
  dsimp [hash_probe_tail_prob]
  rw [hash_probe_expected_cost_sub_const_tail_count]

/-- Translating an offset sequence by subtracting a constant element c in ZMod n preserves the expected probe cost at any load t. -/
theorem hash_probe_expected_cost_sub_const
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (c : ZMod n) (t : ℕ) :
    hash_probe_expected_cost n (fun j => r j - c) t = hash_probe_expected_cost n r t := by
  dsimp [hash_probe_expected_cost]
  simp_rw [hash_probe_expected_cost_sub_const_tail_prob]
