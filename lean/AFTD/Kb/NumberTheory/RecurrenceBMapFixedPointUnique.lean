import AFTD.Prelude
import AFTD.Kb.NumberTheory.RecurrenceBMap
import AFTD.Kb.NumberTheory.RecurrenceBMapZero

/-!
# recurrence_b_map_fixed_point_unique

Topic: elementary_number_theory   Node: 36e46ac16bce

Provenance: helper lemma. arXiv:2610.34300 Proposition 7

For any integer k ≥ 2, a state w in (ℤ/3ℤ)^k is a fixed point of the transition map of recurrence (B) if and only if w is the zero vector.
-/

/-- Unique fixed point of recurrence B is 0 for k ≥ 2. -/
theorem recurrence_b_map_fixed_point_unique (k : ℕ) (hk : 2 ≤ k) (w : Fin k → ZMod 3) : recurrence_b_map k w = w ↔ w = 0 := by
  constructor
  · intro hw
    have hall : ∀ (j : ℕ) (hj : j < k), w ⟨j, hj⟩ = w ⟨0, by omega⟩ := by
      intro j
      induction' j with j ih
      · intro hj
        rfl
      · intro hj
        have hj' : j < k := by omega
        have hstep : (recurrence_b_map k w) ⟨j, hj'⟩ = w ⟨j + 1, hj⟩ := by
          dsimp [recurrence_b_map]
          rw [dif_pos hj]
        have heq : (recurrence_b_map k w) ⟨j, hj'⟩ = w ⟨j, hj'⟩ := by rw [hw]
        rw [hstep] at heq
        rw [heq, ih hj']
    have hlast : (recurrence_b_map k w) ⟨k - 1, by omega⟩ =
        w ⟨0, by omega⟩ + (w ⟨k - 1, by omega⟩)^2 := by
      dsimp [recurrence_b_map]
      have hnot : ¬ (k - 1 + 1 < k) := by omega
      rw [dif_neg hnot]
    have heq_last : (recurrence_b_map k w) ⟨k - 1, by omega⟩ = w ⟨k - 1, by omega⟩ := by
      rw [hw]
    rw [hlast] at heq_last
    have h0_eq : w ⟨k - 1, by omega⟩ = w ⟨0, by omega⟩ := hall (k - 1) (by omega)
    rw [h0_eq] at heq_last
    have hc : w ⟨0, by omega⟩ = 0 := by
      have hdec : ∀ c : ZMod 3, c + c ^ 2 = c → c = 0 := by decide
      exact hdec (w ⟨0, by omega⟩) heq_last
    ext ⟨i, hi⟩
    rw [hall i hi, hc]
    rfl
  · rintro rfl
    exact recurrence_b_map_zero k
