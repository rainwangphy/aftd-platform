import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportBoxThreeEvenSequence
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# davenport_box_three_even_sequence_sum

Topic: elementary_number_theory   Node: 30a3ae618025

Provenance: helper lemma. Step of the proof of Theorem 3 of arXiv:2610.16562 (even m): T(m) sums to zero.

The sequence T(m) (even case) is a zero-sum sequence, for every m ≥ 2.
-/

theorem davenport_box_three_even_sequence_sum (m : ℕ) (hm : 2 ≤ m) :
    (davenport_box_three_even_sequence m).sum = 0 := by
  have hc1 : ((4 * m ^ 3 - 6 * m ^ 2 + 4 * m - 1 : ℕ) : ℤ) =
      4 * (m : ℤ) ^ 3 - 6 * (m : ℤ) ^ 2 + 4 * (m : ℤ) - 1 := by
    have h1 : 6 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
    have h2 : 1 ≤ 4 * m ^ 3 - 6 * m ^ 2 + 4 * m := by omega
    rw [Nat.cast_sub h2]
    push_cast
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hc2 : ((4 * m ^ 3 - 4 * m ^ 2 : ℕ) : ℤ) = 4 * (m : ℤ) ^ 3 - 4 * (m : ℤ) ^ 2 := by
    have h3 : 4 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
    rw [Nat.cast_sub h3]
    push_cast
    ring
  have hc3 : ((4 * m ^ 3 - 2 * m ^ 2 : ℕ) : ℤ) = 4 * (m : ℤ) ^ 3 - 2 * (m : ℤ) ^ 2 := by
    have h4 : 2 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
    rw [Nat.cast_sub h4]
    push_cast
    ring
  dsimp [davenport_box_three_even_sequence]
  simp only [Multiset.sum_add, Multiset.sum_replicate]
  ext i
  fin_cases i <;> simp <;> { rw [hc1, hc2, hc3]; ring }
