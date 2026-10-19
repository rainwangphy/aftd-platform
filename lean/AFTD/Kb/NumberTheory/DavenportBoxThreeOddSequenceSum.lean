import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportBoxThreeOddSequence
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# davenport_box_three_odd_sequence_sum

Topic: elementary_number_theory   Node: b6bf5f73b67d

Provenance: helper lemma. Step of the proof of Theorem 3 of arXiv:2610.16562 (odd m): T(m) sums to zero.

The sequence T(m) (odd case) is a zero-sum sequence, for every m ≥ 2.
-/

lemma davenport_box_three_odd_sequence_sum_cast1 (m : ℕ) (hm : 2 ≤ m) :
    ((4 * m ^ 3 - 8 * m ^ 2 + 5 * m - 2 : ℕ) : ℤ) = 4 * (m : ℤ) ^ 3 - 8 * (m : ℤ) ^ 2 + 5 * (m : ℤ) - 2 := by
  have h1 : 8 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h2 : 2 ≤ 4 * m ^ 3 - 8 * m ^ 2 + 5 * m := by omega
  rw [Nat.cast_sub h2]
  push_cast
  rw [Nat.cast_sub h1]
  push_cast
  ring

lemma davenport_box_three_odd_sequence_sum_cast2 (m : ℕ) (hm : 2 ≤ m) :
    ((4 * m ^ 3 - 2 * m ^ 2 + 2 * m : ℕ) : ℤ) = 4 * (m : ℤ) ^ 3 - 2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) := by
  have h1 : 2 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  push_cast
  rw [Nat.cast_sub h1]
  push_cast
  ring

lemma davenport_box_three_odd_sequence_sum_cast3 (m : ℕ) (hm : 2 ≤ m) :
    ((4 * m ^ 3 - 2 * m ^ 2 + m : ℕ) : ℤ) = 4 * (m : ℤ) ^ 3 - 2 * (m : ℤ) ^ 2 + (m : ℤ) := by
  have h1 : 2 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  push_cast
  rw [Nat.cast_sub h1]
  push_cast
  ring

lemma davenport_box_three_odd_sequence_sum_cast4 (m : ℕ) (hm : 2 ≤ m) :
    ((4 * m ^ 3 - 4 * m ^ 2 + 2 * m : ℕ) : ℤ) = 4 * (m : ℤ) ^ 3 - 4 * (m : ℤ) ^ 2 + 2 * (m : ℤ) := by
  have h1 : 4 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  push_cast
  rw [Nat.cast_sub h1]
  push_cast
  ring

theorem davenport_box_three_odd_sequence_sum (m : ℕ) (hm : 2 ≤ m) :
    (davenport_box_three_odd_sequence m).sum = 0 := by
  dsimp [davenport_box_three_odd_sequence]
  rw [Multiset.sum_add, Multiset.sum_add, Multiset.sum_add]
  rw [Multiset.sum_replicate, Multiset.sum_replicate, Multiset.sum_replicate, Multiset.sum_replicate]
  ext i
  have hc1 := davenport_box_three_odd_sequence_sum_cast1 m hm
  have hc2 := davenport_box_three_odd_sequence_sum_cast2 m hm
  have hc3 := davenport_box_three_odd_sequence_sum_cast3 m hm
  have hc4 := davenport_box_three_odd_sequence_sum_cast4 m hm
  fin_cases i
  · simp [hc1, hc2, hc3, hc4]; ring
  · simp [hc1, hc2, hc3, hc4]; ring
  · simp [hc1, hc2, hc3, hc4]; ring
