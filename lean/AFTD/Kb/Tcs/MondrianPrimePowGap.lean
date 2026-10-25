import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_prime_pow_gap

Topic: combinatorics   Node: 4ffe4e29903c

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

For p at least two, c less than p, and r at least two, c times r plus one is less than p to the r.
-/

theorem mondrian_prime_pow_gap (c p r : ℕ) (hp : 2 ≤ p) (hpc : c < p)
    (hr : 2 ≤ r) : (r + 1) * c < p ^ r := by
  suffices h : ∀ j : ℕ, (j + 3) * c < p ^ (j + 2) by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h j
  intro j
  induction j with
  | zero =>
    simp only [Nat.zero_add, pow_two]
    by_cases hp2 : p = 2
    · subst p
      interval_cases c <;> norm_num
    · have hp3 : 3 ≤ p := by omega
      have hm := Nat.mul_le_mul_right p hp3
      omega
  | succ j ih =>
    have hle : (j + 4) * c ≤ p * ((j + 3) * c) := by
      have hm := Nat.mul_le_mul_right ((j + 3) * c) hp
      nlinarith
    calc
      (j + 1 + 3) * c ≤ p * ((j + 3) * c) := by simpa [Nat.add_assoc] using hle
      _ < p * p ^ (j + 2) := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ = p ^ (j + 1 + 2) := by simpa only [Nat.mul_comm] using (pow_succ p (j + 2)).symm
