import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.LinearProbeOffset
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlotsCard
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# prime_fixed_offset_linear_probe_tail_prob_interior_t_pred

Topic: data_structures   Node: d51974ae4825

Provenance: helper lemma. step towards prime_fixed_offset_linear_probe_tail_prob_interior_le

At load t = p - 1 (one empty slot), every bijective offset sequence has identical probe tail probabilities, matching linear probing.
-/

private lemma prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_probe_fiber_card
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Injective r) (occ : Finset (ZMod n)) (hocc : occ.card = n - 1)
    (k : ℕ) (hk : k ≤ n - 1) :
    (Finset.univ.filter (fun q : ZMod n => ∀ j : Fin n, j.val < k → q + r j ∈ occ)).card
      = n - k := by
  have hcard_univ : (Finset.univ : Finset (ZMod n)).card = n := by
    rw [Finset.card_univ, ZMod.card]
  have hcompl : occᶜ.card = 1 := by
    rw [Finset.card_compl, ZMod.card, hocc]
    have hp : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcompl
  have hmem : ∀ x : ZMod n, x ∈ occ ↔ x ≠ e := by
    intro x
    have hx : x ∈ occᶜ ↔ x ∈ ({e} : Finset (ZMod n)) := by rw [he]
    simp only [Finset.mem_compl, Finset.mem_singleton] at hx
    constructor
    · intro h1 h2; exact (hx.mpr h2) h1
    · intro h1; by_contra h2; exact h1 (hx.mp h2)
  set J : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < k) with hJ
  set B : Finset (ZMod n) := J.image (fun j => e - r j) with hB
  have hS : (Finset.univ.filter (fun q : ZMod n => ∀ j : Fin n, j.val < k → q + r j ∈ occ))
      = (Finset.univ : Finset (ZMod n)) \ B := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro h hqB
      rw [hB, hJ, Finset.mem_image] at hqB
      obtain ⟨j, hj, hq⟩ := hqB
      rw [Finset.mem_filter] at hj
      obtain ⟨-, hjk⟩ := hj
      have hconj : q + r j = e := by rw [← hq]; abel
      exact (hmem _).mp (h j hjk) hconj
    · intro hqB j hjk
      rw [hmem]
      intro hq_eq
      apply hqB
      rw [hB, hJ, Finset.mem_image]
      exact ⟨j, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hjk⟩, by rw [← hq_eq]; abel⟩
  rw [hS, Finset.card_sdiff, Finset.inter_univ, hcard_univ]
  have hBcard : B.card = k := by
    rw [hB, Finset.card_image_of_injective _ ?_]
    · rw [hJ, Fin.card_filter_val_lt, Nat.min_eq_right (by omega)]
    · intro j1 j2 h
      simp only at h
      have h' : r j1 = r j2 := by
        have := congrArg (fun x => e - x) h
        simpa using this
      exact hr h'
  rw [hBcard]

private lemma prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_tail_count_common
    (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (k : ℕ) (hk : k ≤ n - 1) :
    hash_probe_tail_count n r (n - 1) k = ∑ _A : Fin (n - 1) → ZMod n, (n - k) := by
  have h1 : hash_probe_tail_count n r (n - 1) k
      = ∑ x : (Fin (n - 1) → ZMod n) × ZMod n,
          (if (∀ j : Fin n, j.val < k → x.2 + r j ∈ hash_occupied_slots n r (List.ofFn x.1))
            then (1:ℕ) else 0) := by
    rw [hash_probe_tail_count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [← Finset.card_filter]
  exact prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_probe_fiber_card n r hr.injective _ (by
    rw [hash_occupied_slots_card n r hr (List.ofFn A) (by simp)]
    simp) k hk

private lemma prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_linear_probe_injective
    (p : ℕ) [NeZero p] : Function.Injective (linear_probe_offset p) := by
  intro j1 j2 h
  simp only [linear_probe_offset] at h
  have h' : (j1.val : ℕ) % p = (j2.val : ℕ) % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rw [Nat.mod_eq_of_lt j1.isLt, Nat.mod_eq_of_lt j2.isLt] at h'
  exact Fin.ext h'

private lemma prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_linear_probe_bijective
    (p : ℕ) [NeZero p] : Function.Bijective (linear_probe_offset p) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_linear_probe_injective p,
    by simp [ZMod.card]⟩

/-- At load t = p - 1 (one empty slot), every bijective offset sequence has identical probe tail probabilities, matching linear probing. -/
theorem prime_fixed_offset_linear_probe_tail_prob_interior_t_pred
    (p : ℕ) [Fact (Nat.Prime p)]
    (r : Fin p → ZMod p) (hr_bij : Function.Bijective r) (hr0 : r 0 = 0)
    (k : ℕ) (hk2 : 2 ≤ k) (hkt : k ≤ p - 1) (ht : p - 1 < p) :
    hash_probe_tail_prob p r (p - 1) k ≤ hash_probe_tail_prob p (linear_probe_offset p) (p - 1) k := by
  have h_eq : hash_probe_tail_count p r (p - 1) k
      = hash_probe_tail_count p (linear_probe_offset p) (p - 1) k := by
    rw [prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_tail_count_common p r hr_bij k hkt,
      prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_tail_count_common p
        (linear_probe_offset p)
        (prime_fixed_offset_linear_probe_tail_prob_interior_t_pred_linear_probe_bijective p) k hkt]
  unfold hash_probe_tail_prob
  rw [h_eq]
