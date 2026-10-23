import AFTD.Prelude

/-!
# circulant_cycle_remainder_bound

Topic: graphs   Node: 55b052e0fabc

Provenance: helper lemma. step towards circulant_mixed_graph_no_cycle_lt_g

For t < g and steps with quotient q_i ∈ {0, 1} and remainder r_i bounded by (z+1)/2 (and at most z/2 when q_i = 1), the sum of remainders R satisfies R ≤ m, and if Q = ∑ q_i is odd then R < m.
-/

/-- For t < g and steps with quotient q_i ∈ {0, 1} and remainder r_i bounded by (z+1)/2 (and at most z/2 when q_i = 1), the sum of remainders R satisfies R ≤ m, and if Q = ∑ q_i is odd then R < m. -/
theorem circulant_cycle_remainder_bound (z g t : ℕ) (hz : 1 ≤ z) (hg : 3 ≤ g) (ht : t < g)
    (q r : Fin t → ℕ) (hq : ∀ i, q i ≤ 1) (hr : ∀ i, r i ≤ (z + 1) / 2)
    (hr_q : ∀ i, q i = 1 → r i ≤ z / 2) :
    let N := if Even z then z * (g - 1) + 2 else (z + 1) * (g - 1)
    let m := N / 2
    let Q := ∑ i : Fin t, q i
    let R := ∑ i : Fin t, r i
    R ≤ m ∧ (Odd Q → R < m) := by
  open Finset in
  intro N m Q R
  by_cases heven : Even z
  · have hN : N = z * (g - 1) + 2 := if_pos heven
    have hm : m = (z / 2) * (g - 1) + 1 := by
      dsimp [m]
      rw [hN]
      obtain ⟨k, rfl⟩ := heven
      have h1 : (k + k) * (g - 1) + 2 = 2 * (k * (g - 1)) + 2 := by ring
      have h2 : (k + k) / 2 = k := by omega
      rw [h1, h2]
      omega
    have hR : R ≤ t * (z / 2) := by
      dsimp [R]
      have hr' : ∀ i, r i ≤ z / 2 := by
        intro i
        have := hr i
        obtain ⟨k, rfl⟩ := heven
        omega
      simpa using sum_le_card_nsmul (univ : Finset (Fin t)) r (z / 2) (fun i _ => hr' i)
    have ht_le : t * (z / 2) ≤ (g - 1) * (z / 2) :=
      Nat.mul_le_mul_right (z / 2) (Nat.le_pred_of_lt ht)
    have hcomm : (g - 1) * (z / 2) = (z / 2) * (g - 1) := mul_comm _ _
    have hlt : R < m := by omega
    exact ⟨le_of_lt hlt, fun _ => hlt⟩
  · have hN : N = (z + 1) * (g - 1) := if_neg heven
    have hodz : Odd z := Nat.not_even_iff_odd.mp heven
    obtain ⟨k, rfl⟩ := hodz
    have hm : m = ((2 * k + 1 + 1) / 2) * (g - 1) := by
      dsimp [m]
      rw [hN]
      have h1 : (2 * k + 1 + 1) * (g - 1) = 2 * ((k + 1) * (g - 1)) := by ring
      have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [h1, h2]
      omega
    have hR_le_t : R ≤ t * ((2 * k + 1 + 1) / 2) := by
      dsimp [R]
      simpa using sum_le_card_nsmul (univ : Finset (Fin t)) r ((2 * k + 1 + 1) / 2) (fun i _ => hr i)
    have ht_le : t * ((2 * k + 1 + 1) / 2) ≤ (g - 1) * ((2 * k + 1 + 1) / 2) :=
      Nat.mul_le_mul_right ((2 * k + 1 + 1) / 2) (Nat.le_pred_of_lt ht)
    have hcomm : (g - 1) * ((2 * k + 1 + 1) / 2) = ((2 * k + 1 + 1) / 2) * (g - 1) := mul_comm _ _
    have hR_le_m : R ≤ m := by omega
    refine ⟨hR_le_m, fun hQ => ?_⟩
    have hj : ∃ j : Fin t, q j = 1 := by
      by_contra! h
      have h0 : ∀ i : Fin t, q i = 0 := by
        intro i
        have := hq i
        have := h i
        omega
      have hsum : Q = 0 := by
        dsimp [Q]
        simp [h0]
      rw [hsum] at hQ
      exact Nat.not_odd_zero hQ
    obtain ⟨j, hj1⟩ := hj
    have hrj : r j < (2 * k + 1 + 1) / 2 := by
      have := hr_q j hj1
      omega
    have hR_lt_t : R < t * ((2 * k + 1 + 1) / 2) := by
      dsimp [R]
      have h1 : ∑ i : Fin t, r i < ∑ i : Fin t, ((2 * k + 1 + 1) / 2) := by
        apply sum_lt_sum
        · intro i _
          exact hr i
        · exact ⟨j, mem_univ j, hrj⟩
      have h2 : ∑ i : Fin t, ((2 * k + 1 + 1) / 2) = t * ((2 * k + 1 + 1) / 2) := by simp
      omega
    omega
