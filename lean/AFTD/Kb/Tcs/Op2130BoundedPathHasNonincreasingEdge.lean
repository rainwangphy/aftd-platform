import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_2130_bounded_path_has_nonincreasing_edge

Topic: online_algorithms   Node: a35d5f6c1238

Provenance: helper lemma. OP-2130: existence of a legal potential-increasing move before the threshold

If D is positive and each of 2D integer discrepancies has absolute value below D, some adjacent pair is non-increasing from left to right.
-/

theorem op_2130_bounded_path_has_nonincreasing_edge (D : ℕ) (hD : 1 ≤ D) (d : Fin (2 * D) → ℤ) (h : ∀ i, |d i| < (D : ℤ)) : ∃ i : Fin (2 * D - 1), d ⟨i.val, by omega⟩ ≥ d ⟨i.val + 1, by omega⟩ := by
  by_contra hcon
  push_neg at hcon
  let f : ℕ → ℤ := fun n => d ⟨min n (2 * D - 1), by omega⟩
  have hstep : ∀ i ∈ Finset.range (2 * D - 1), (1 : ℤ) ≤ f (i + 1) - f i := by
    intro i hi
    have hi' : i < 2 * D - 1 := Finset.mem_range.mp hi
    have hlt : d ⟨i, by omega⟩ < d ⟨i + 1, by omega⟩ := by
      simpa using hcon ⟨i, hi'⟩
    simp only [f]
    have hmin1 : min i (2 * D - 1) = i := Nat.min_eq_left (le_of_lt hi')
    have hmin2 : min (i + 1) (2 * D - 1) = i + 1 := Nat.min_eq_left (by omega)
    simp only [hmin1, hmin2]
    omega
  have hsum : ((2 * D - 1 : ℕ) : ℤ) ≤ ∑ i ∈ Finset.range (2 * D - 1), (f (i + 1) - f i) := by
    calc
      ((2 * D - 1 : ℕ) : ℤ) = ∑ i ∈ Finset.range (2 * D - 1), (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ Finset.range (2 * D - 1), (f (i + 1) - f i) := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub] at hsum
  have hflast : f (2 * D - 1) = d ⟨2 * D - 1, by omega⟩ := by
    simp [f]
  have hf0 : f 0 = d ⟨0, by omega⟩ := by
    simp [f]
  rw [hflast, hf0] at hsum
  have h0 := (abs_lt.mp (h ⟨0, by omega⟩)).1
  have hlast := (abs_lt.mp (h ⟨2 * D - 1, by omega⟩)).2
  omega
